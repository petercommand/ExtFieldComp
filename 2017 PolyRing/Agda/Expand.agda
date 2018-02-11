open import Data.Nat
open import Data.Vec
open import Num
open import PolyRing renaming (fmap to Pfmap)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties.Simple
record Extended (F : Set → Set) (n : ℕ) : Set₁ where
  field
    fromVec : ∀ {A : Set} → Vec A n → F A
    toVec : ∀ {A : Set} → F A → Vec A n

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B : Set} → (A → B) → F A → F B

open Functor {{...}}

genInd : ∀ {A : Set} (n : ℕ) → Vec (ExprN A n) n
genInd zero = []
genInd (suc zero) = Ind ∷ []
genInd (suc (suc n)) = Ind ∷ (map Lit (genInd (suc n)))

expand : ∀ {A : Set} (n : ℕ) (F : Set → Set)
  → {{func : Functor F}}
  → {{num : Num A}} → {{ext : Extended F n}}
  → {{numE : Num (F (ExprN A n))}}
  → Expr (F A)
  → F (ExprN A n)
expand n F = foldExpr (fromVec (genInd n))
   (fmap (liftExpr (≤→≤′ 0 n z≤n)))
  where
   open Extended {{...}}


fmapN' : ∀ {A B : Set} (m : ℕ)
  → (A → B)
  → ExprN A m
  → ExprN B m
fmapN' zero f e = f e
fmapN' (suc m) f e = Pfmap (fmapN' m f) e

expand'-step : ∀ {A : Set} (m n k : ℕ) (F : Set → Set)
  → (func : Functor F)
  → (num : Num A) → (ext : Extended F n)
  → (numE : ∀ n → Num (F (ExprN A n)))
  → (∀ {A} → (num : Num A) → (ext : Extended F n) → (numE : Num (F (ExprN A n)))
      → (Expr (F A)) → F (ExprN A n))
  → ExprN (F (ExprN A m)) (suc k)
  → ExprN (F (ExprN A (m + n))) k
expand'-step {A} m n k F func num ext numE base e
  = subst (λ x → ExprN (F x) k) (ExprN-comb {A} m n)
      (fmapN' k (base {ExprN A m} (toExprNumN m {{num}}) ext
                  (subst (λ x → Num (F x)) (sym (ExprN-comb m n)) (numE (m + n))))
                      (subst (λ x → x) (sym (numEquiv (F (ExprN A m)) k)) e))


expand'-aux :
  ∀ {A : Set} (n k : ℕ) (F : Set → Set)
  → {{func : Functor F}}
  → {{ext : Extended F n}}
  → (∀ n → Num (ExprN A n))
  → (∀ n → Num (F (ExprN A n)))
  → (∀ {A} → (num : Num A) → (ext : Extended F n) → (numE : Num (F (ExprN A n)))
      → (Expr (F A)) → F (ExprN A n))
  → ExprN (F A) k → F (ExprN A (k * n))
expand'-aux n zero F base numAn numE e = e
expand'-aux {A} n (suc zero) F {{func}} {{ext}} numAn numE base
  = subst (λ x → Expr (F A) → F (ExprN A x))
       (+-comm 0 n) (base (numAn 0) ext (numE n))
expand'-aux {A} n (suc (suc k)) F {{func}} {{ext}} numAn numE base e
  = subst F (ExprN-comb {A} n (n + k * n))
          (expand'-aux n (suc k) F (λ n₁ → subst Num (sym (ExprN-comb n n₁)) (toExprNumN (n + n₁) {{numAn 0}}))
             (λ n₁ → subst (λ x → Num (F x)) (sym (ExprN-comb n n₁)) (numE (n + n₁))) base
             (expand'-step {A} 0 n (suc k) F func (numAn 0) ext numE base e))


expand' : ∀ {A : Set} (n : ℕ) (F : Set → Set)
  → {{func : Functor F}}
  → {{num : Num A}} → {{ext : Extended F n}}
  → (∀ m → Num (F (ExprN A m)))
  → ∀ k
  → ExprN (F A) k
  → F (ExprN A (k * n))
expand' {A} n F {{func}} num k
     = expand'-aux n k F {{_}} {{_}} (λ n₁ → toExprNumN {A} n₁) num 
         (λ {A} num' ext' numE' → expand {A} n F {{func}} {{num'}} {{ext'}} {{numE'}})
  where
   open Extended {{...}}

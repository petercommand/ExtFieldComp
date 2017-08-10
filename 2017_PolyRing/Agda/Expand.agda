open import Data.Nat
open import Data.Vec
open import Num
open import PolyRing hiding (fmap)
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
expand n F = foldExpr (fromVec (genInd n)) (fmap (liftExpr (≤→≤′ 0 n z≤n)))
  where
   open Extended {{...}}

expand'-aux :
  ∀ {A : Set} (n k : ℕ) (F : Set → Set)
  → {{func : Functor F}}
  → {{num : Num A}} → {{ext : Extended F n}}
  → {{numE : Num (F (ExprN A n))}}
  → (∀ {A} → (num : Num A) → (ext : Extended F n) → (numE : Num (F (ExprN A n)))
      → (Expr (F A)) → F (ExprN A n))
  → ExprN (F A) k → F (ExprN A (k * n))
expand'-aux n zero F base e = e
expand'-aux {A} n (suc zero) F {{func}} {{num}} {{ext}} {{numE}} base
  = subst (λ x → Expr (F A) → F (ExprN A x)) (+-comm 0 n) (base num ext numE)
expand'-aux {A} n (suc (suc k)) F base e
  = subst (λ x → Expr (F (ExprN A (n + k * n))) → F (ExprN A x))
     (trans (+-assoc n (k * n) n) (cong (λ t → n + t) (+-comm (k * n) n)))
     (subst (λ x → Expr (F (ExprN A (n + k * n))) → F x)
        (ExprN-comm (n + k * n) n) (base {ExprN A (n + k * n)} {!!} {!!} {!!}))
          (fmap {_} {Expr (ExprN (F A) k)} {F (ExprN A (n + k * n))}
              (expand'-aux {A} n (suc k) F base) {!!} {!!}) -- (fmap {!! expand'-aux {A} n (suc k) F base !!} e)

expand' : ∀ {A : Set} (n : ℕ) (F : Set → Set)
  → {{func : Functor F}}
  → {{num : Num A}} → {{ext : Extended F n}}
  → (∀ m → Num (F (ExprN A m)))
  → ∀ k
  → ExprN (F A) k
  → F (ExprN A (k * n))
expand' n F {{func}} {{numi}} {{ext}} num k
     = expand'-aux n k F {{_}} {{_}} {{_}} {{num n}}
         (λ {A} num' ext' numE' → expand {A} n F {{func}} {{num'}} {{ext'}} {{numE'}})
  where
   open Extended {{...}}


{-


expand = foldExpr (Complex Ind (Lit Ind)) (fmap (Lit . Lit))

expand (Lit (1, 2))

= foldExpr (Ind, (Lit Ind)) (fmap (Lit . Lit)) (Lit (1, 2))
= Lit (Lit (1, 2))



-}

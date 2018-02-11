module PolyRing where

open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (_⊔_)
open import Data.List
open import Data.Product
open import Data.Vec hiding (_>>=_) renaming (_++_ to _v++_)
open import Num
open import NatProperties
open import Data.Nat.Properties.Simple
open import Level hiding (zero; suc)
open import Function
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality

data Expr {l} (A : Set l) : Set l where
  Ind : Expr A
  Lit : (x : A) -> Expr A
  Add : (e1 : Expr A) -> (e2 : Expr A) -> Expr A
  Sub : (e1 : Expr A) -> (e2 : Expr A) -> Expr A
  Mul : (e1 : Expr A) -> (e2 : Expr A) -> Expr A

foldExpr : ∀ {m} {a : Set m} {b : Set} {{num : Num b}}
         -> b
         -> (a -> b)
         -> Expr a
         -> b
foldExpr x f Ind = x
foldExpr _ f (Lit x) = f x
foldExpr {{num}} x f (Add e1 e2) =
   let _+_ = Num._+_ num
   in foldExpr x f e1 + foldExpr x f e2
foldExpr {{num}} x f (Sub e1 e2) =
   let _-_ = Num._-_ num
   in foldExpr x f e1 - foldExpr x f e2
foldExpr {{num}} x f (Mul e1 e2) =
   let _*_ = Num._*_ num
   in foldExpr x f e1 * foldExpr x f e2

ExprN : ∀ {l} (A : Set l) (n : ℕ) -> Set l
ExprN A zero = A
ExprN A (suc n) = Expr (ExprN A n)

Expr2 : ∀ {l} (A : Set l) -> Set l
Expr2 A = ExprN A (suc (suc zero))

DChain : Set -> ℕ -> Set
DChain A zero = ⊤
DChain A (suc n) = ExprN A n × DChain A n

liftExpr : ∀ {l} {A : Set l} {m n : ℕ} → m ≤′ n → ExprN A m → ExprN A n
liftExpr {m = m} {.m} ≤′-refl e = e
liftExpr {m = m} {.(suc _)} (≤′-step p) e = Lit (liftExpr p e)

liftVal : ∀ {l}{A : Set l} n → A → ExprN A n
liftVal zero x = x
liftVal (suc n) x = Lit (liftVal n x)

instance toFuncNum : ∀ {A : Set} (num : Num A) -> Num (A -> A)
toFuncNum record { _+_ = _+_ ; _-_ = _-_ ; _*_ = _*_ }
   = record { _+_ = \f g x -> f x + g x
            ; _-_ = \f g x -> f x - g x
            ; _*_ = \f g x -> f x * g x
            }

instance toExprNum : ∀ {A : Set} (num : Num A) -> Num (Expr A)
toExprNum record { _+_ = _+_ ; _-_ = _-_ ; _*_ = _*_ }
   = record { _+_ = \e1 e2 -> Add e1 e2
            ; _-_ = \e1 e2 -> Sub e1 e2
            ; _*_ = \e1 e2 -> Mul e1 e2
            }

fmap : ∀ {A B : Set} -> (A -> B) -> Expr A -> Expr B
fmap f Ind = Ind
fmap f (Lit x) = Lit (f x)
fmap f (Add e e₁) = Add (fmap f e) (fmap f e₁)
fmap f (Sub e e₁) = Sub (fmap f e) (fmap f e₁)
fmap f (Mul e e₁) = Mul (fmap f e) (fmap f e₁)

numEquiv : ∀ (A : Set) (n : ℕ) -> ExprN (Expr A) n ≡ Expr (ExprN A n)
numEquiv _ zero = refl
numEquiv _ (suc n) = cong Expr (numEquiv _ n)

ExprN-comb : ∀ {A : Set} m n → ExprN (ExprN A m) n ≡ ExprN A (m + n)
ExprN-comb zero n = refl
ExprN-comb {A} (suc m) n rewrite numEquiv (ExprN A m) n = cong Expr (ExprN-comb m n)

compose : ∀ {A : Set} -> (n : ℕ) -> (A -> A) -> (A -> A)
compose zero f = id
compose (suc n) f = f ∘ compose n f

fmapN : ∀ {A : Set}{m} -> (n : ℕ) -> (ExprN A m -> ExprN A m) -> ExprN A (m + n) -> ExprN A (m + n)
fmapN {_} {m} zero f rewrite +-comm m zero = f
fmapN {A} {m} (suc n) f rewrite a+suc-b==suc-a+b m n
   = fmapN {_} {suc m} n (fmap f)

toExprNumN : ∀ {A : Set} (n : ℕ){{num : Num A}} -> Num (ExprN A n)
toExprNumN zero {{num}} = num
toExprNumN {A} (suc n) {{num}} =
   toExprNum (toExprNumN n)

-- Semantics

semantics1 : ∀ {A : Set} {{num : Num A}} → Expr A → A → A
semantics1 = foldExpr id const

semantics : ∀ {A : Set}{{num : Num A}} (n : ℕ) → ExprN A n → DChain A n → A
semantics zero x tt = x
semantics {A} (suc n) e (t , es) =
    semantics n (semantics1 {{toExprNumN n}} e t) es

sem-lem+ : ∀ {A : Set} {{num : Num A}} (n : ℕ)
  → (e₁ e₂ : ExprN A n)
  → (es : DChain A n)
  → semantics n (Num._+_ (toExprNumN n) e₁ e₂) es ≡
    Num._+_ num (semantics n e₁ es)
                (semantics n e₂ es)
sem-lem+ zero e₁ e₂ _ = refl
sem-lem+ {{num}} (suc n) e₁ e₂ (en , es) =
   sem-lem+ n (semantics1 {{toExprNumN n}} e₁ en)
              (semantics1 {{toExprNumN n}} e₂ en) es

sem-lem- : ∀ {A : Set} {{num : Num A}} (n : ℕ)
  → (e₁ e₂ : ExprN A n)
  → (es : DChain A n)
  → semantics n (Num._-_ (toExprNumN n) e₁ e₂) es ≡
    Num._-_ num (semantics n e₁ es)
                (semantics n e₂ es)
sem-lem- zero e₁ e₂ _ = refl
sem-lem- {{num}} (suc n) e₁ e₂ (en , es) =
   sem-lem- n (semantics1 {{toExprNumN n}} e₁ en)
              (semantics1 {{toExprNumN n}} e₂ en) es

sem-lem* : ∀ {A : Set} {{num : Num A}} (n : ℕ)
  → (e₁ e₂ : ExprN A n)
  → (es : DChain A n)
  → semantics n (Num._*_ (toExprNumN n) e₁ e₂) es ≡
    Num._*_ num (semantics n e₁ es)
                (semantics n e₂ es)
sem-lem* zero e₁ e₂ _ = refl
sem-lem* {{num}} (suc n) e₁ e₂ (en , es) =
   sem-lem* n (semantics1 {{toExprNumN n}} e₁ en)
              (semantics1 {{toExprNumN n}} e₂ en) es

-- Rotation

idExpr2 : ∀ {A : Set} {{num : Num A}} → Expr2 A → Expr2 A
idExpr2 = foldExpr {{toExprNumN 2}} Ind
            (foldExpr {{toExprNumN 2}} (Lit Ind) (Lit ∘ Lit))

rotaExpr2 : ∀ {A : Set} {{num : Num A}} → Expr2 A → Expr2 A
rotaExpr2 = foldExpr {{toExprNumN 2}} (Lit Ind)
              (foldExpr {{toExprNumN 2}} Ind (Lit ∘ Lit))

rotaExprN : ∀ {A : Set} {{num : Num A}} (n : ℕ) → ExprN A n → ExprN A n
rotaExprN zero = id
rotaExprN (suc zero) = id
rotaExprN (suc (suc zero)) = rotaExpr2
rotaExprN (suc (suc (suc n))) = subst (λ x → Expr (Expr x) → Expr (Expr x)) (numEquiv _ n)
                                      (fmapN {_} {1} (suc n) rotaExpr2 ∘ rotaExprN {{toExprNumN 1}} (suc (suc n)))

rotaExprN-m : ∀ {A : Set} {{num : Num A}} (n m : ℕ) → ExprN A n → ExprN A n
rotaExprN-m n zero e = e
rotaExprN-m n (suc m) e = rotaExprN-m n m (rotaExprN n e)


Vec→DChain : ∀ {A : Set} (n : ℕ) → Vec A n → DChain A n
Vec→DChain zero [] = tt
Vec→DChain (suc n) (x ∷ xs) = liftVal n x , Vec→DChain n xs

substitute : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> ExprN A n -> Vec (ExprN A n) n -> ExprN A n
substitute {A} n e e'
   = semantics {ExprN A n} {{toExprNumN {A} n}} n
        (subst id (sym (ExprN-comb {A} n n))
          (rotaExprN-m (n + n) n
             (liftExpr {_} {_} {n} {n + n}
               (≤→≤′ n (n + n) (≤-weakening n n n ≤-refl)) e)))
        (Vec→DChain n e')

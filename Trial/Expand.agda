module _ where

open import Data.Product
open import Data.Nat

Nest : ℕ → Set → Set
Nest zero A = A
Nest (suc n) A = Nest n A × Nest n A

data Expr (A : Set): Set where
  num : A → Expr A
  _∔_ : (e₀ : Expr A) → (e₁ : Expr A) → Expr A

expand1 : ∀ {n A} → Expr (Nest (suc n) A) → (Expr (Nest n A) × Expr (Nest n A))
expand1 (num (x , y)) = num x , num y
expand1 {n} {A} (e₀ ∔ e₁) with expand1 {n} e₀ | expand1 {n} e₁
... | u₀ , u₁ | t₀ , t₁ = u₀ ∔ t₀ , u₁ ∔ t₁

expand : ∀ {n A} → Expr (Nest n A) → Nest n (Expr A)
expand = ? 

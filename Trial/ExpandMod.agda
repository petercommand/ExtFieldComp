module _ where

open import Level hiding (suc;zero)

open import Data.Nat
open import Data.Vec
open import Data.Product using (_×_;_,_)

open import Relation.Binary.Core

NestMod : (A : Set) (n : ℕ) → Vec ℕ n → Set
NestMod A zero [] = A
NestMod A (suc n) (x ∷ vec) = Vec (NestMod A n vec) x


data Expr (A : Set) : Set where
  num : A → Expr A
  _∔_ : (e₀ : Expr A) → (e₁ : Expr A) → Expr A

Op₂ : Set -> Set
Op₂ A = A -> A -> A

NestF : (A : Set) (n : ℕ) → Vec ℕ n → Set
NestF A zero [] = Op₂ A
NestF A (suc n) (x ∷ vec) = Op₂ (Vec (Expr (NestMod A n vec)) x) × NestF A n vec

NestObj : (A : Set) (n : ℕ) → Vec ℕ n → Set
NestObj A zero [] = A
NestObj A (suc n) (x ∷ vec) = Vec (Expr (NestMod A n vec)) x × NestObj A n vec


expand1 : ∀ {A} (n : ℕ)
   → (len : ℕ)
   → (vec : Vec ℕ n)
   → Expr (NestMod A (suc n) (len ∷ vec)) → Vec (Expr (NestMod A n vec)) len
expand1 n len vec (num x) = map num x
expand1 {A} n len vec (exp₀ ∔ exp₁)
   = let e₀ = expand1 n len vec exp₀
         e₁ = expand1 n len vec exp₁
     in zipWith (_∔_) e₀ e₁

expand : ∀ {A} (n : ℕ)
   → (vec : Vec ℕ n)
   → (op : NestF A n vec)
   → (target : NestObj A n vec)
   → Expr (NestMod A n vec)
   → NestMod (Expr A) n vec
expand zero [] _ _ exp = exp
expand (suc n) (x ∷ vec) (op , opᵣ) (target , targetᵣ) exp
  = map (expand n vec opᵣ targetᵣ) (op (expand1 n x vec exp) target)

module _ where

open import Data.Nat
open import Data.Vec

NestMod : (n : ℕ) → Vec ℕ n → Set → Set
NestMod zero [] A = A
NestMod (suc n) (x ∷ vec) A = Vec (NestMod n vec A) x

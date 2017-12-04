module _ where
open import Data.Nat hiding (_+_)
open import Data.Nat.Primality
open import Data.Integer
open import Data.List
open import Data.Sign as Sign

data Fp (n : ℕ) .(p : Prime n) : Set where
  F : ℤ -> Fp n p

data Poly (K : Set) : Set where
  P : (x : List K) -> length x > 0 -> Poly K

deg : {K : Set} -> Poly K -> ℕ
deg (P x x₁) = length x


data ExtF (K : Set) (x : Poly K) : Set where
  Ext : (poly : Poly K) -> ExtF K x



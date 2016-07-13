module _ where
open import Data.Nat hiding (_+_)
open import Data.Nat.Primality
open import Data.Integer
open import Data.List
open import Data.Sign as Sign

data Fp (n : ℕ) : Set where
  F : (x : ℕ) -> .{{p : Prime n}} -> Fp n

data Poly (K : Set) : Set where
  P : List K -> Poly K

data ExtF {P} (K : Set) (x : Poly P) : Set where
  Ext : Poly K -> ExtF K x



import Data.Nat
open import Data.Nat.Primality
import Data.Integer
import Data.Sign as Sign
open import Function
open import Data.List
open import Data.Product
open import Data.Bool
open Data.Nat hiding (_+_; _*_)
open Data.Integer using (ℤ; _◃_)

open import Relation.Binary.PropositionalEquality
open import NatProperties
record Num (A : Set) : Set where
  field
    _+_ : A -> A -> A
    _-_ : A -> A -> A
    _*_ : A -> A -> A

ℕ- : (a b : ℕ) -> a ≥ b -> ℕ
ℕ- a .0 z≤n = a
ℕ- (suc m) (suc n) (s≤s p) = ℕ- m n p


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

record AddMul (A : Set) : Set where
  field
    _+_ : A -> A -> A
    _*_ : A -> A -> A


ℕ- : (a b : ℕ) -> a ≥ b -> ℕ
ℕ- a .0 z≤n = a
ℕ- (suc m) (suc n) (s≤s p) = ℕ- m n p

≤′-suc : ∀ a b → a ≤′ b → suc a ≤′ suc b
≤′-suc a .a ≤′-refl = ≤′-refl
≤′-suc a .(suc _) (≤′-step p) = ≤′-step (≤′-suc a _ p)

≤→≤′ : ∀ a b → a ≤ b → a ≤′ b
≤→≤′ zero zero = λ x → ≤′-refl
≤→≤′ zero (suc b) z≤n = ≤′-step (≤→≤′ zero b z≤n)
≤→≤′ (suc a) zero ()
≤→≤′ (suc a) (suc b) (s≤s p) = ≤′-suc a b (≤→≤′ a b p)

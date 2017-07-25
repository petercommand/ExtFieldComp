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

ℕ--suc : ∀ (a : ℕ) p -> ℕ- (suc a) a p ≡ 1
ℕ--suc zero z≤n = refl
ℕ--suc (suc a) (s≤s p) = ℕ--suc a p

ℕ-refl : ∀ (a : ℕ) p -> ℕ- a a p ≡ 0
ℕ-refl zero z≤n = refl
ℕ-refl (suc a) (s≤s p) = ℕ-refl a p


ℕ-0 : ∀ (n : ℕ) ->  (p : 0 ≤ n) -> ℕ- n 0 p ≡ n
ℕ-0 n z≤n = refl

ℕ-inv : ∀ (i n : ℕ) -> (p : i ≥ n) -> ℕ- (suc i) (suc n) (s≤s p) ≡ ℕ- i n p
ℕ-inv zero zero p = refl
ℕ-inv (suc i) zero p = refl
ℕ-inv i (suc n) p = refl

module CommutativeRing where
open import Data.Product
open import Num
open import Relation.Binary.PropositionalEquality

record CommutativeRing
   (A : Set) (num : Num A) (_≈_ : A → A → Set) : Set where
  open Num.Num num
  field

    -- Abelian Group (Addition)
    +-assoc : ∀ a b c → (a + (b + c)) ≈ ((a + b) + c)
    +-comm : ∀ a b → (a + b) ≈ (b + a)
    +-ε : A
    +-id : ∀ a → (a + +-ε) ≈ a  
    +-inv : ∀ a → ∃ λ a⁻¹ → (a + a⁻¹) ≈ +-ε

    -- Monoid (Multiplication)

    *-assoc : ∀ a b c → (a * (b * c)) ≈ ((a * b) * c)
    *-comm : ∀ a b → (a * b) ≈ (b * a)
    *-ε : A
    *-id : ∀ a → (*-ε * a) ≈ a

    -- Multiplication is Distributive over Addition

    left-dist : ∀ a b c → (a * (b + c)) ≈ ((a * b) + (a * c))
    right-dist : ∀ a b c → ((b + c) * a) ≈ ((b * a) + (c * a))




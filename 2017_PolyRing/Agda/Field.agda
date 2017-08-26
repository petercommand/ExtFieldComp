module Field where
open import Data.Product
open import Num
open import Relation.Binary.PropositionalEquality

record Field
   (A : Set) (am : AddMul A) (_≈_ : A → A → Set) : Set where
  open AddMul am
  field

    -- Abelian Group (Addition)
    +-assoc : ∀ a b c → (a + (b + c)) ≈ ((a + b) + c)
    +-comm : ∀ a b → (a + b) ≈ (b + a)
    +-ε : A
    +-id : ∀ a → (a + +-ε) ≈ a  
    +-inv : ∀ a → ∃ λ a⁻¹ → (a + a⁻¹) ≈ +-ε

    -- Multiplication

    *-assoc : ∀ a b c → (a * (b * c)) ≈ ((a * b) * c)
    *-comm : ∀ a b → (a * b) ≈ (b * a)
    *-ε : A
    *-id : ∀ a → (*-ε * a) ≈ a
    *-inv : ∀ a → ∃ λ a⁻¹ → (a * a⁻¹) ≈ *-ε

    -- Multiplication is Distributive over Addition

    left-dist : ∀ a b c → (a * (b + c)) ≈ ((a * b) + (a * c))
    right-dist : ∀ a b c → ((b + c) * a) ≈ ((b * a) + (c * a))




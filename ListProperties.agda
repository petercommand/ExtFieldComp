module _ where
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality
open import NatProperties

++-assoc : ∀ {K : Set} (a b c : List K) -> a ++ b ++ c ≡ (a ++ b) ++ c
++-assoc [] b c = refl
++-assoc (x ∷ a) b c = cong (_∷_ x) (++-assoc a b c)

++-length : ∀ {K : Set}(a b : List K) -> length a ≥ 0 -> length b > 0 -> length (a ++ b) > 0
++-length [] b p1 p2 = p2
++-length (x ∷ a) b z≤n p2 = s≤s (≤weak (++-length a b z≤n p2))

last : ∀ {l} {K : Set l} -> (l : List K) -> length l > 0 -> K
last [] ()
last (x ∷ []) p = x
last (x ∷ x₁ ∷ l₁) (s≤s p) = last (x₁ ∷ l₁) (s≤s z≤n)

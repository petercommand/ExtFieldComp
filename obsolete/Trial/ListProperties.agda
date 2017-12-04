module _ where

open import Data.List
open import Relation.Binary.PropositionalEquality

++-assoc : ∀ {K : Set} (a b c : List K) -> a ++ b ++ c ≡ (a ++ b) ++ c
++-assoc [] b c = refl
++-assoc (x ∷ a) b c = cong (_∷_ x) (++-assoc a b c)

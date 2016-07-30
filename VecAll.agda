module _ where
open import Level
open import Data.Vec

data VecAll {a p} {A : Set a}
         (P : A → Set p) : ∀ {n} → Vec A n → Set (p ⊔ a) where
  AllB  : VecAll P []
  AllI : ∀ {n}{x : A} {xs : Vec A n} (px : P x) (pxs : VecAll P xs)
          → VecAll P (x ∷ xs)


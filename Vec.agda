module _ where

open import Data.Product hiding (map; zip)
open import Data.Vec hiding (map; zip; zipWith) public

map : ∀ {a b n} {A : Set a} {B : Set b} →
      (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

zipWith : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c} →
          (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith _⊕_ [] [] = []
zipWith _⊕_ (x ∷ xs) (x₁ ∷ ys) = x ⊕ x₁ ∷ zipWith _⊕_ xs ys

zip : ∀ {a b n} {A : Set a} {B : Set b} →
      Vec A n → Vec B n → Vec (A × B) n
zip = zipWith _,_

module MaybeUtil where

open import Data.Maybe

maybeComb : ∀ {l m}{A : Set l}{B : Set m} -> Maybe A -> (f : A -> Maybe B) -> Maybe B
maybeComb (just x) f = f x
maybeComb nothing f = nothing

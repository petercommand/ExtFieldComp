module _ where
open import Field
open import Num
open import Data.List
open import Function
K = Fp 5
_+K_ = Num._+_ $ numPoly {K}
K2 = ExtF K (_+K_ (x ^ 2) 1)
  where
    x = P (0 ∷ 1 ∷ [])

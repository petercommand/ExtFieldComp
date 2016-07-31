module _ where
open import Data.Nat
open import Data.Nat.Primality


open import Field
open import Num
open import Data.List
open import Function

postulate
   p5 : Prime 5

K = Fp 5 p5
np = numPoly {K} {{numFp {_} {{p5}} {{numℕ}}}}
_+K_ = Num._+_ $ numPoly {K} {{numFp {_} {{p5}} {{numℕ}}}}
_^_ = _^'_ {{np}}

K2 = ExtF K ((x ^ 2) +K (P ((F 1) ∷ [])))
  where
    x : Poly K
    x = P (F 0 ∷ F 1 ∷ [])


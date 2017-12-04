open import Data.Bool
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Product


open import Expand
open import Expr
open import Num


numBool : Num Bool
numBool = record { +-id = false ; *-id = true ; _+_ = _xor_ ; _-_ = _xor_ ; _*_ = _∧_ }

GF4 = NestMod Bool 1 (2 ∷ [])

GF2 = NestMod Bool 0 []

testGF4 : Expr1 GF4 0 -- NestMod (Expr1 GF2 0) 1 (2 ∷ [])
testGF4 = LetC1 (true ∷ false ∷ []) (Mul1 (Var1 zero) (Var1 zero))

testExpand : NestMod (Expr1 GF2 0) 1 (2 ∷ [])
testExpand = let f = λ _ x1 x2 →    let a1 = head x1
                                        a0 = head (tail x1)
                                        b1 = head x2
                                        b0 = head (tail x2)
                                        r1 = Add1 (Mul1 a1 b0) (Add1 (Mul1 a0 b1) (Mul1 a1 b1))
                                        r2 = Add1 (Mul1 a0 b0) (Mul1 a1 b1)
                                    in r1 ∷ r2 ∷ []
             in expand 1 (2 ∷ []) (f , (λ x1 x2 → x1 ∧ x2)) testGF4

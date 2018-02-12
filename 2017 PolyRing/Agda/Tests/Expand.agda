module Tests.Expand where

open import Data.Vec
open import Data.Nat
open import Data.Integer hiding (_*_)
open import Data.Product

open import PolyRing
open import Expand
open import Num

open import Tests.Instance

open Integer

testExpandComplex : ℂ (ExprN ℤ 2)
testExpandComplex = expand 2 ℂ (Lit (ℤ.pos 5 , ℤ.negsuc 3))
  where
    open Tests.Instance.Complex ℤ


testExpandComplex2 : ℂ (ExprN ℤ 4)
testExpandComplex2 = expand' 2 ℂ (λ m → toℂNum m (toExprNumN m)) 2 expr
  where
    expr : Expr (Expr (ℂ ℤ))
    expr = Mul (Lit Ind) (Add Ind (Lit (Add Ind (Lit (ℤ.pos 10 , ℤ.negsuc 3)))))

    toℂNum : ∀ m → Num (ExprN ℤ m) → Num (ℂ (ExprN ℤ m))
    toℂNum m ins = ℂNum
      where
        open Complex (ExprN ℤ m)
        instance
          i = ins

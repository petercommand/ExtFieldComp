module Tests.Semantics where

open import Data.Unit
open import Data.Product
open import Data.Integer as ℤ
open import Relation.Binary.PropositionalEquality

open import PolyRing
open import Num

open import Tests.Instance

open Tests.Instance.Complex ℤ

sem-test0 : semantics 1 Ind ((Lit (ℤ.negsuc 4)) , tt) ≡ Lit (ℤ.negsuc 4)
sem-test0 = refl



-- Ind -> x which is 3+9i
-- Lit Ind -> y which is -11-4i
-- y + (x * (7 + 6i))
sem-test1 : semantics 2 (Add (Lit Ind)
                      (Mul Ind (Lit (Lit (ℤ.pos 7 , ℤ.pos 6)))))
                           (Lit (ℤ.pos 3 , ℤ.pos 9) , ((ℤ.negsuc 10 , ℤ.negsuc 3) , tt))
          ≡ (ℤ.negsuc 43 , ℤ.pos 77) 
sem-test1 = refl


module _ where

open import Data.Nat
open import Data.Nat.Primality
open import Data.Product
open import Data.Maybe
open import Data.Vec
open import Data.String
open import Data.List
open import Data.Fin
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core

open import RTEnv
open import Env
open import Comp
open import CompVerify
open import FpComp
open import Field
open import Num
open import NatProperties
open import Expr
open import MaybeUtil

eq' : ∀ {A : Set} (vec : Vec A 1) -> head vec ∷ [] ≡ vec
eq' (x ∷ []) = refl
fpVerify : ∀ {m n : ℕ}{{p : Prime n}}
         (varnum : ℕ)
         (rtenv : RTEnv)
         (evalEnv : EvalEnv (Fp n p) m)
         (env : Env 1 (1 ∷ []) m)
         (cons : EnvConsistent (Fp n p) 1 (1 ∷ [])
           (\x -> fpToInt {n} {{p}} x ∷ [])
           (\x -> F (head x))
           eq'
           evalEnv env rtenv varnum)
         (expr : Expr1 (Fp n p) m)
         -> let varnum1 , ir1 , r1 = fpToIR (varnum , env) expr
            in getBatch r1 (run rtenv ir1) ≡
               fpToInt (evalNum' {{numFp {n} {{p}}}} evalEnv expr)
                 ∷ []
fpVerify rtenv evalEnv env cons expr = {!!}

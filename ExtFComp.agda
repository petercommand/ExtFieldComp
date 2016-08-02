open import Agda.Builtin.Int
open import Data.Nat
open import Data.Integer hiding (suc; _*_)
open import Data.Maybe
open import Data.Nat.Primality
open import Data.Product
open import Data.List
open import Data.Vec as Vec hiding (_++_)

open import Relation.Binary.PropositionalEquality

open import Function

open import MaybeUtil
open import Comp
open import Expr
open import Env
open import Field
open import RTEnv
open import Num

extfToIR : ∀ {o K x} -> {{compK : Compilable K}}
                     -> CompState (deg x * Compilable.compSize compK) o
                     -> Expr1 (ExtF K x) o
                     -> ℕ × List TAC × Vec Addr (deg x * Compilable.compSize compK)
extfToIR (varnum , env) (Let1 exp exp₁)
   = let varnum1 , ir1 , r1 = extfToIR (varnum , env) exp
         varnum2 , ir2 , r2 = extfToIR (varnum1 , r1 ∷ env) exp₁
     in varnum2 , ir2 , r2
extfToIR (varnum , env) (LetC1 (Ext (P x₁ x₂)) exp)
   = let varnum1 , ir1 , r1 = flatCompMap x₁
     in {!extToIR (varnum1 , (r1 ∷ env)) exp!}
extfToIR st (Var1 x₁) = {!!}
extfToIR st (Add1 exp exp₁) = {!!}
extfToIR st (Mul1 exp exp₁) = {!!}

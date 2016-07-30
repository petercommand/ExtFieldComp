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
open import FpComp
open import Field
open import Num
open import NatProperties
open import Expr
open import MaybeUtil


addrMonoInc : {m n o : ℕ}{{p : Prime o}}(env : Env 1 m)(expr : Expr1 (Fp o) m)
                        -> fst (fpToIR {_} {{p}} (n , env) expr) > n
addrMonoInc {_} {n} {{p}} env e = {!!}
-- compEq' : ∀ {m n varnum : ℕ}{{p : Prime n}}

{-
fpConsistent : {m n : ℕ} (rtenv : RTEnv)
                       (env : Env 1 m)
                       (expr : Expr1 (Fp n) m)
                       {{p : Prime n}}
                       {{ins : Num (Fp n)}}
                       -> (r : Fp n)
                       -> (envc : EnvConsistent env rtenv)
                       -> ins ∙ (fpEnvToEvalEnvTotal {{p}} env rtenv) $ expr ↓ r
-}
compEq : ∀ {m n varnum : ℕ}{{p : Prime n}}
                           (rtenv : RTEnv)
                           (env : Env 1 m)
                           (expr : Expr1 (Fp n) m)
                           -> let compResult = fpToIR (varnum , env) expr
                              in fpRunWRTEnv {{p}} {{numFp {_} {p} {{numℕ}}}} rtenv (proj₂ compResult) ≡
                                 (maybeComb (fpEnvToEvalEnv {{p}} env rtenv) (\evalEnv -> just (evalNum' {{numFp {_} {p} {{numℕ}}}} evalEnv expr)))
compEq rtenv env e = {!!}

{-
 compPreserve : ∀ {n : ℕ} {p : Prime n} -> (sp : Compilable.compSize (fpCompilable {n} {p}) ≡ 1)

fpVerify : ∀ {n : ℕ} {p : Prime n} -> (expr : Expr1 (Fp n) 0)
                                   -> just (evalNum {{numFp {_} {p} {{numℕ}}}} expr) ≡ fpRunComp {{p}} {{fpCompilable {n} {p}}} refl expr
fpVerify {n} {p} expr = sym (compEq {{p}} [] [] expr) 
 prove that fpToIR (.varnum , env) (LetC1 (F x) expr) ≡ fpToIR (_varnum_244 env x expr , (x ∷ []) ∷ env) expr
-}


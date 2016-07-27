module _ where
open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Show
open import Data.Fin
open import Data.Integer using (ℤ)
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.String
open import Data.Maybe
open import Data.Bool
open import Data.Nat.Primality
open import Data.Vec using (Vec; foldr)
open import Function
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality

open import Field
open import Expr
open import RTEnv

Env : ℕ -> ℕ -> Set
Env m n = Vec (Vec ℕ m) n -- List of [Address]

EvalEnv : Set -> ℕ -> Set
EvalEnv K n = Vec K n

fpEnvToEvalEnv : {m : ℕ}{n : ℕ}{{_ : Prime m}} -> Env 1 n -> RTEnv -> Maybe (EvalEnv (Fp m) n)
fpEnvToEvalEnv Vec.[] rtenv = just Vec.[]
fpEnvToEvalEnv ((x Vec.∷ Vec.[]) Vec.∷ env) rtenv with rtLookup x rtenv
fpEnvToEvalEnv {m} {{p}} ((x Vec.∷ Vec.[]) Vec.∷ env) rtenv | just result with fpEnvToEvalEnv {m} {_} {{p}} env rtenv
fpEnvToEvalEnv ((x Vec.∷ Vec.[]) Vec.∷ env) rtenv | just result | just x₂ = just (F result Vec.∷ x₂)
fpEnvToEvalEnv ((x Vec.∷ Vec.[]) Vec.∷ env) rtenv | just result | nothing = nothing
fpEnvToEvalEnv ((x Vec.∷ Vec.[]) Vec.∷ env) rtenv | nothing = nothing


lookup : {m n : ℕ} -> Fin n -> Env m n -> Vec ℕ m
lookup zero (x Vec.∷ env) = x
lookup (suc num) (x Vec.∷ env) = lookup num env

evalLookup : {K : Set}{n : ℕ} -> Fin n -> EvalEnv K n -> K
evalLookup zero (x Vec.∷ env) = x
evalLookup (suc n) (x Vec.∷ env) = evalLookup n env

putEnvVal : ∀ {m n} -> Vec ℕ m -> Env m n -> Env m (suc n)
putEnvVal x env = x Vec.∷ env

CompState : ℕ -> ℕ -> Set
CompState m n = ℕ × Env m n

getCompResultVarnum : {n o : ℕ} -> CompState n o × List TAC × Vec Addr n -> ℕ
getCompResultVarnum ((varnum , _) , _ , _) = varnum

getCompResultEnv : {n o : ℕ} -> CompState n o × List TAC × Vec Addr n -> Env n o
getCompResultEnv ((_ , env) , _ , _) = env

getCompResultIR : {n o : ℕ} -> CompState n o × List TAC × Vec Addr n -> List TAC
getCompResultIR (_ , ir , _) = ir

getCompResultAddr : {n o : ℕ} -> CompState n o × List TAC × Vec Addr n -> Vec Addr n
getCompResultAddr (_ , _ , r) = r


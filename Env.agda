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
open import Data.Vec using (Vec)
open import Function
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality

open import Expr
open import RTEnv

Env : ℕ -> ℕ -> Set
Env m n = Vec (Vec ℕ m) n -- List of [Address]

EvalEnv : Set -> ℕ -> Set
EvalEnv K n = Vec K n


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

getCompResultIR : {n o : ℕ} -> CompState n o × List TAC × Vec Addr n -> List TAC
getCompResultIR (_ , ir , _) = ir

getCompResultAddr : {n o : ℕ} -> CompState n o × List TAC × Vec Addr n -> Vec Addr n
getCompResultAddr (_ , _ , r) = r


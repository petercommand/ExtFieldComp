module _ where
open import Data.Nat
open import Data.Fin
open import Data.Integer using (ℤ)
open import Data.Product
open import Data.Nat.Primality
open import Data.Vec hiding (lookup)

open import Field
open import Expr
open import RTEnv


Env : ℕ -> ℕ -> Set
Env m n = Vec (Vec ℕ m) n -- List of [Address]

EvalEnv : Set -> ℕ -> Set
EvalEnv K n = Vec K n


lookup : {m n : ℕ} -> Fin n -> Env m n -> Vec ℕ m
lookup zero (x ∷ env) = x
lookup (suc num) (x ∷ env) = lookup num env

evalLookup : {K : Set}{n : ℕ} -> Fin n -> EvalEnv K n -> K
evalLookup zero (x ∷ env) = x
evalLookup (suc n) (x ∷ env) = evalLookup n env

putEnvVal : ∀ {m n} -> Vec ℕ m -> Env m n -> Env m (suc n)
putEnvVal x env = x ∷ env

CompState : ℕ -> ℕ -> Set
CompState m n = ℕ × Env m n



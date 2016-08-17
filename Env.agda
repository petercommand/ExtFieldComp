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

Env : (m : ℕ) -> (vec : Vec ℕ m) -> ℕ -> Set
Env m vec n = Vec (NestMod ℕ m vec) n  -- Vec (Vec ℕ m) n -- List of [Address]

EvalEnv : Set -> ℕ -> Set
EvalEnv K n = Vec K n

lookup : {m n : ℕ} -> (vec : Vec ℕ m) -> Fin n -> Env m vec n -> NestMod ℕ m vec
lookup vec zero (x ∷ env) = x
lookup vec (suc num) (x ∷ env) = lookup vec num env

evalLookup : {K : Set}{n : ℕ} -> Fin n -> EvalEnv K n -> K
evalLookup zero (x ∷ env) = x
evalLookup (suc n) (x ∷ env) = evalLookup n env

putEnvVal : ∀ {m n} -> (vec : Vec ℕ m)
    -> NestMod ℕ m vec
    -> Env m vec n
    -> Env m vec (suc n)
putEnvVal vec x env = x ∷ env

CompState : (m : ℕ) -> (vec : Vec ℕ m) -> ℕ -> Set
CompState m vec n = ℕ × Env m vec n

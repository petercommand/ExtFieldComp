module _ where

open import Data.Nat
open import Data.Product hiding (map)
open import Data.List hiding (map)
open import Data.Vec
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
Addr : Set
Addr = ℕ

RTEnv : Set
RTEnv = List (Addr × ℕ)

postulate
  putRTEnv : Addr -> ℕ -> RTEnv -> RTEnv
  getRTEnv : Addr -> RTEnv -> ℕ
  get-put : ∀ c k h -> getRTEnv c (putRTEnv c k h) ≡ k
  get-put' : ∀ {k} c c' h -> ¬ c ≡ c' -> getRTEnv c (putRTEnv c' k h) ≡ getRTEnv c h


getBatch : ∀ {n} -> Vec Addr n -> RTEnv -> Vec ℕ n
getBatch [] rtenv = []
getBatch (x ∷ vec) rtenv = getRTEnv x rtenv ∷ vec

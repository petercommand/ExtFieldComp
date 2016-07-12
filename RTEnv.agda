module _ where

open import Data.Nat
open import Data.Integer
open import Data.List
open import Data.Product
open import Data.List.Any
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
RTEnv : Set
RTEnv = List (ℕ × ℕ)


rtLookup : (n : ℕ) -> (env : RTEnv) -> Maybe ℕ
rtLookup n [] = nothing
rtLookup n ((proj₁ , proj₂) ∷ env) with Data.Nat._≟_ n proj₁
rtLookup n ((.n , proj₂) ∷ env) | yes refl = just proj₂
... | no p = rtLookup n env

rtInsert : (ℕ × ℕ) -> RTEnv -> RTEnv
rtInsert n env = n ∷ env

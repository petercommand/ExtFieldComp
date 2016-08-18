module _ where


open import Data.Nat
open import Data.Nat.Primality
open import Data.Integer hiding (_≤_)
open import Data.Product
open import Data.Maybe hiding (All)
open import Data.Vec hiding (_++_)
open import Data.List hiding (product)
open import Data.List.All
open import Data.Fin hiding (_<_; _≤_)
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core

open import RTEnv
open import Env
open import Comp
open import Field
open import Num
open import NatProperties
open import Expr
open import VecAll


data EnvConsistent (K : Set) (m : ℕ)
     (vec : Vec ℕ m)
     (from : K -> Vec ℤ (product vec))
     (to : Vec ℤ (product vec) -> K)
     (p : ∀ n -> from (to n) ≡ n)
     : ∀ {n}
     -> (evalEnv : EvalEnv K n)
     -> (env : Env m vec n)
     -> (rtenv : RTEnv)
     -> ℕ
     -> Set where
  ConsBase : ∀ {n}{rtenv : RTEnv} -> EnvConsistent K m vec from to p [] [] rtenv n
  ConsInd : ∀ {n addrs v o q}
             -> {evalEnv : EvalEnv K n}
             -> {env : Env m vec n}
             -> {rtenv : RTEnv}
             -> getBatch addrs rtenv ≡ from v
             -> VecAll (\a -> a < o) addrs 
             -> o ≤ q
             -> EnvConsistent K m vec from to p evalEnv env rtenv o
             -> EnvConsistent K m vec from to p (v ∷ evalEnv)
                   (addrs ∷ env) rtenv q


consist-inc : ∀ {K m n vec from to p q s}
                {evalEnv : EvalEnv K n}
                {env : Env m vec n}
                {rtenv : RTEnv}
                -> EnvConsistent K m vec from to p evalEnv env rtenv q
                -> q ≤ s
                -> EnvConsistent K m vec from to p evalEnv env rtenv s
consist-inc ConsBase p₁ = ConsBase
consist-inc (ConsInd x x₁ x₂ consist) p₁ = ConsInd x x₁ (≤-trans x₂ p₁) consist

run-compose : ∀ r1 r2 rtenv ->
    run rtenv (r1 ++ r2) ≡ run (run rtenv r1) r2
run-compose [] r2 rtenv = refl
run-compose (ConstI x x₁ ∷ r1) r2 rtenv
  = run-compose r1 r2 (putRTEnv x x₁ rtenv)
run-compose (AddI x x₁ x₂ ∷ r1) r2 rtenv
  = run-compose r1 r2
      (putRTEnv x
         (getRTEnv x₁ rtenv Data.Integer.+
          getRTEnv x₂ rtenv)
       rtenv)
run-compose (SubI x x₁ x₂ ∷ r1) r2 rtenv
  = run-compose r1 r2
      (putRTEnv x
         (getRTEnv x₁ rtenv Data.Integer.-
          getRTEnv x₂ rtenv)
       rtenv)
run-compose (MulI x x₁ x₂ ∷ r1) r2 rtenv
  = run-compose r1 r2
      (putRTEnv x
         (getRTEnv x₁ rtenv Data.Integer.*
          getRTEnv x₂ rtenv)
       rtenv)

vecAllInc : ∀ {n a b}{vec : Vec ℕ n}
   -> a ≤ b
   -> VecAll (\x -> x < a) vec
   -> VecAll (\x -> x < b) vec
vecAllInc p AllB = AllB
vecAllInc p (AllI px vecAll) = AllI (≤-trans px p) (vecAllInc p vecAll)

consist : ∀ {K m n vec from to p env rtenv q}{evalEnv : EvalEnv K n}
   -> EnvConsistent K m vec from to p evalEnv env rtenv q
   -> ∀ x
   -> getBatch (Env.lookup vec x env) rtenv ≡ from (evalLookup x evalEnv)
consist {vec = []} ConsBase ()
consist {vec = x ∷ vec} ConsBase ()
consist (ConsInd x x₁ x₂ cons) zero = x
consist (ConsInd x x₁ x₂ cons) (Fin.suc x₃) = consist cons x₃

consist->vecAll : ∀ {K m n vec from to p env rtenv q}{evalEnv : EvalEnv K n}
   -> EnvConsistent K m vec from to p evalEnv env rtenv q
   -> ∀ x
   -> VecAll (\a -> a < q) (Env.lookup vec x env)
consist->vecAll ConsBase ()
consist->vecAll (ConsInd x x₁ x₂ cons) zero = vecAllInc x₂ x₁
consist->vecAll (ConsInd x x₁ x₂ cons) (Fin.suc x₃)
   = vecAllInc x₂ (consist->vecAll cons x₃)

consist-reduce : ∀ {K m n vec from to p ee e env rtenv q}{evalEnv : EvalEnv K n}
   -> EnvConsistent K m vec from to p (ee ∷ evalEnv) (e ∷ env) rtenv q
   -> EnvConsistent K m vec from to p evalEnv env rtenv q
consist-reduce (ConsInd x x₁ x₂ consist) = consist-inc consist x₂

getBatchLem : ∀ {n r k rtenv t}{addrs : Vec ℕ n}
   -> VecAll (\a -> a < r) addrs
   -> getBatch addrs rtenv ≡ t
   -> getBatch addrs (putRTEnv r k rtenv) ≡ t
getBatchLem AllB bat = bat
getBatchLem {_} {r} {k} {rtenv} (AllI {x = x} px vec) refl
  rewrite get-put' {k} x r rtenv (a<c->¬a≡c x r px)
   = cong (λ y → getRTEnv x rtenv ∷ y) (getBatchLem vec refl)

rpc-aux : ∀ {k K m n vec from to p env rtenv q r s}{evalEnv : EvalEnv K n}
   -> r ≥ q
   -> s ≥ r
   -> EnvConsistent K m vec from to p evalEnv env rtenv q
   -> EnvConsistent K m vec from to p evalEnv env (putRTEnv r k rtenv) s
rpc-aux x y ConsBase = ConsBase
rpc-aux x y (ConsInd x₁ x₂ x₃ consist)
   = ConsInd (getBatchLem (vecAllInc x (vecAllInc x₃ x₂)) x₁)
        (vecAllInc x (vecAllInc x₃ x₂)) y
        (rpc-aux (≤-trans x₃ x) ≤-refl consist)

++-rewrite : ∀ {l}{K : Set l}(a : K)(b : List K)(c : List K)
            -> a Data.List.∷ b Data.List.++ c ≡
               a ∷ (b Data.List.++ c)
++-rewrite a [] c = refl
++-rewrite a (x ∷ b) c = refl

_:>_ : ∀ {l} (K : Set l) (a : K) -> K
a :> b = b



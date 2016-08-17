module _ where


open import Data.Nat
open import Data.Nat.Primality
open import Data.Integer hiding (_≤_)
open import Data.Product
open import Data.Maybe hiding (All)
open import Data.Vec
open import Data.String
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
open import MaybeUtil
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
  ConsBase : ∀ {rtenv : RTEnv} -> EnvConsistent K m vec from to p [] [] rtenv 0
  ConsInd : ∀ {n addrs v o q}
             -> {evalEnv : EvalEnv K n}
             -> {env : Env m vec n}
             -> {rtenv : RTEnv}
             -> getBatch addrs rtenv ≡ from v
             -> VecAll (\a -> a < o) addrs 
             -> o ≤ q
             -> EnvConsistent K m vec from to p evalEnv env rtenv o
             -> EnvConsistent K m vec from to p (v ∷ evalEnv)
                   (reconstruct _ vec addrs ∷ env) rtenv q

++-rewrite : ∀ {l}{K : Set l}(a : K)(b : List K)(c : List K)
            -> a Data.List.∷ b Data.List.++ c ≡ a ∷ (b Data.List.++ c)
++-rewrite a [] c = refl
++-rewrite a (x ∷ b) c = refl

_:>_ : ∀ {l} (K : Set l) (a : K) -> K
a :> b = b

nothing-just : ∀ {K : Set} -> {a : K} -> ¬ (nothing ≡ (Maybe K :> just a))
nothing-just {a} ()


evalNum'->big : ∀ {K : Set} -> {{ins : Num K}}
                            -> {m : ℕ}
                            -> (env : EvalEnv K m)
                            -> (expr : Expr1 K m)
                            -> (r : K)
                            -> evalNum' env expr ≡ r
                            -> ins ∙ env $ expr ↓ r
evalNum'->big {{ins}} env (Let1 expr expr₁) .(evalNum' (evalNum' env expr ∷ env) expr₁) refl =
  let r = evalNum' env expr
  in bigLet1 (evalNum'->big env expr r refl)
         (evalNum'->big (r ∷ env) expr₁ (evalNum' (r ∷ env) expr₁) refl)
evalNum'->big env (LetC1 x expr) r ev rewrite sym ev
    = bigLetC1 $ evalNum'->big (x ∷ env) expr (evalNum' (x ∷ env) expr) refl
evalNum'->big env (Var1 x) .(evalLookup x env) refl = bigVar1 x
evalNum'->big env (Add1 expr expr₁) _ refl
    = bigAdd1 (evalNum'->big env expr (evalNum' env expr) refl)
          (evalNum'->big env expr₁ (evalNum' env expr₁) refl)
evalNum'->big env (Mul1 expr expr₁) _ refl
    = bigMul1 (evalNum'->big env expr (evalNum' env expr) refl)
          (evalNum'->big env expr₁ (evalNum' env expr₁) refl)

big->evalNum' : ∀ {K : Set} -> {{ins : Num K}}
                            -> {m : ℕ}
                            -> (env : EvalEnv K m)
                            -> (expr : Expr1 K m)
                            -> (r : K)
                            -> ins ∙ env $ expr ↓ r
                            -> evalNum' env expr ≡ r
big->evalNum' {_} {{_}} {m} env (Let1 expr expr₁) r (bigLet1 big big₁)
      rewrite big->evalNum' env expr _ big
            | big->evalNum' (_ ∷ env) expr₁ r big₁ = refl
big->evalNum' env (LetC1 x expr) r (bigLetC1 big)
      rewrite big->evalNum' (x ∷ env) expr r big = refl
big->evalNum' env (Var1 n) .(evalLookup n env) (bigVar1 .n) = refl
big->evalNum' env (Add1 expr expr₁) _ (bigAdd1 big big₁)
      rewrite big->evalNum' env expr _ big
            | big->evalNum' env expr₁ _ big₁ = refl
big->evalNum' env (Mul1 expr expr₁) _ (bigMul1 big big₁)
      rewrite big->evalNum' env expr _ big
            | big->evalNum' env expr₁ _ big₁ = refl

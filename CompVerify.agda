module _ where


open import Data.Nat
open import Data.Nat.Primality
open import Data.Integer hiding (_≤_)
open import Data.Product
open import Data.Maybe hiding (All)
open import Data.Vec hiding (_++_)
open import Data.List hiding (product)
open import Data.List.All
open import Data.List.All.Properties
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


HeapInc : ∀ {K n vec o}
   -> (toIR : CompState n vec o
                -> Expr1 K o
                -> ℕ × List TAC × Vec Addr (product vec))
   -> Set
HeapInc {K} {n} {vec} {o} toIR
   = ∀ varnum env expr -> let varnum1 , ir1 , r1 = toIR (varnum , env) expr
                          in varnum1 ≥ varnum

AddrInc : ∀ {K n vec o}
    -> (toIR : CompState n vec o
                -> Expr1 K o
                -> ℕ × List TAC × Vec Addr (product vec))
    -> Set
AddrInc toIR = ∀ varnum env expr -> let _ , ir , _ = toIR (varnum , env) expr
                                    in All (\x -> target x ≥ varnum) ir

comp-irrelevance' : ∀ {a b list} -> All (\x -> b ≤ target x) list
                                 -> a < b
                                 -> All (\x -> ¬ x ≡ a) (Data.List.map target list)
comp-irrelevance' [] p = []
comp-irrelevance' (px ∷ all) p = (a<c->¬c≡a _ _ (≤-trans p px)) ∷
                                    comp-irrelevance' all p

comp-irrelevance : ∀ {K n vec o}(toIR : CompState n vec o
                                    -> Expr1 K o
                                    -> _) varnum varnum1
   -> varnum < varnum1
   -> HeapInc {K} {n} {vec} toIR
   -> AddrInc {K} {n} {vec} toIR
   -> ∀ expr env
   -> let _ , ir , _ = toIR (varnum1 , env) expr
      in All (\x -> ¬ x ≡ varnum) (Data.List.map target ir)
comp-irrelevance toIR varnum varnum1 p inc all expr env
    with inc varnum env expr
... | inc1
    with all varnum1 env expr
... | all1
    with toIR (varnum1 , env) expr
... | varnum2 , ir1 , r1 = comp-irrelevance' all1 p

list-decomp : ∀ (ir : List TAC) -> length ir > 0
    -> ∃ (λ x -> ∃ (λ y -> (x ++ (y ∷ [])) ≡ ir))
list-decomp [] ()
list-decomp (x ∷ []) (s≤s p) = [] , x , refl
list-decomp (x ∷ x₁ ∷ ir) (s≤s p)
   = let head , elem , pr = list-decomp (x₁ ∷ ir) (s≤s z≤n)
     in x ∷ head , elem , cong (\y -> x ∷ y) pr

all-decomp : ∀ {K : Set}{P : K -> Set}(list : List K) (all : All P list) -> length list > 0
    -> ∃ (λ x -> ∃ (λ y -> All P x × All P (y ∷ []) × (x ++ (y ∷ []) ≡ list) × (length x < length list)))
all-decomp [] [] ()
all-decomp (x ∷ []) (px ∷ []) (s≤s p) = [] , x , [] , px ∷ [] , refl , s≤s z≤n
all-decomp (x ∷ xs ∷ xss) (px ∷ px₁ ∷ all) p = let head , elem , headp , elemp , pr , pr2 = all-decomp (xs ∷ xss) (px₁ ∷ all) (s≤s z≤n)
                                               in x ∷ head , elem , px ∷ headp , elemp , cong (\y -> x ∷ y) pr , s≤s pr2

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

ignorable : ∀ addr rtenv ir -> All (\x -> ¬ target x ≡ addr) ir
                   -> Acc (length ir)
                   -> getRTEnv addr (run rtenv ir) ≡ getRTEnv addr rtenv
ignorable addr rtenv [] [] _ = refl
ignorable addr rtenv (x₅ ∷ ir) all (acc ac) with all-decomp (x₅ ∷ ir) all (s≤s z≤n)
... | head , ConstI x x₁ , allh , e ∷ alle , pr , pr2
    rewrite sym pr
          | run-compose head (ConstI x x₁ ∷ []) rtenv
          | get-put' {x₁} addr x (run rtenv head) (e ∘ sym)
          = ignorable addr rtenv head allh (ac (length head) pr2)
... | head , AddI x x₁ x₂ , allh , e ∷ alle , pr , pr2
    rewrite sym pr
          | run-compose head (AddI x x₁ x₂ ∷ []) rtenv
          | get-put' {getRTEnv x₁ (run rtenv head) Data.Integer.+
                      getRTEnv x₂ (run rtenv head)} addr x (run rtenv head) (e ∘ sym)
          = ignorable addr rtenv head allh (ac (length head) pr2)
... | head , SubI x x₁ x₂ , allh , e ∷ alle , pr , pr2
    rewrite sym pr
          | run-compose head (SubI x x₁ x₂ ∷ []) rtenv
          | get-put' {getRTEnv x₁ (run rtenv head) Data.Integer.-
                      getRTEnv x₂ (run rtenv head)} addr x (run rtenv head) (e ∘ sym)
          = ignorable addr rtenv head allh (ac (length head) pr2)
... | head , MulI x x₁ x₂ , allh , e ∷ alle , pr , pr2
    rewrite sym pr
          | run-compose head (MulI x x₁ x₂ ∷ []) rtenv
          | get-put' {getRTEnv x₁ (run rtenv head) Data.Integer.*
                      getRTEnv x₂ (run rtenv head)} addr x (run rtenv head) (e ∘ sym)
          = ignorable addr rtenv head allh (ac (length head) pr2)
comp-ignorable : ∀ {K n vec o}(toIR : CompState n vec o
                                    -> Expr1 K o
                                    -> _) varnum varnum1
   -> varnum < varnum1
   -> HeapInc {K} {n} {vec} {o} toIR
   -> AddrInc {K} {n} {vec} {o} toIR
   -> ∀ expr env rtenv
   -> let _ , ir , _ = toIR (varnum1 , env) expr
      in getRTEnv varnum (run rtenv ir) ≡ getRTEnv varnum rtenv
comp-ignorable {K} {n} {vec} {o} toIR varnum varnum1 p inc all expr env rtenv
   = let irre = comp-irrelevance {K} {n} {vec} toIR varnum varnum1 p inc all expr env
         _ , ir , _ = toIR (varnum1 , env) expr
     in ignorable varnum rtenv ir (map-All irre) (<-wf (length ir))

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

All<weak : ∀ {a}{list : List TAC} -> All (\x -> a ≤ target x) list
                                         -> ∀ b
                                         -> b ≤ a
                                         -> All (\x -> b ≤ target x) list
All<weak [] b p = []
All<weak (px ∷ all) b p = (≤-trans p px) ∷ (All<weak all b p)

All++ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys : List A} →
        All P xs → All P ys → All P (xs ++ ys)
All++ []         pys = pys
All++ (px ∷ pxs) pys = px ∷ All++ pxs pys


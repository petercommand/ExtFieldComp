module _ where


open import Data.Nat
open import Data.Nat.Primality
open import Data.Product
open import Data.Maybe
open import Data.Vec
open import Data.String
open import Data.List
open import Data.Fin

open import Relation.Binary.PropositionalEquality

open import RTEnv
open import Env
open import Comp
open import Field
open import Num
open import NatProperties
open import Expr

open import Function

data Consistent {k : ℕ} {{_ : Prime k}} : {m n : ℕ} -> (varnum : ℕ) -> EvalEnv (Fp k) n -> Env 1 n -> Vec Addr m -> RTEnv -> Set where
  Cbase : ∀ {rtenv : RTEnv} -> Consistent 0 [] [] [] rtenv
  Cinc : ∀ {n : ℕ}{varnum : ℕ} -> (evalEnv : EvalEnv (Fp k) n)
                               -> (env : Env 1 n)
                               -> (addr : Vec Addr n)
                               -> (rtEnv : RTEnv)
                               -> Consistent varnum evalEnv env addr rtEnv
                               -> (Svarnum : ℕ)
                               -> Svarnum > varnum
                               -> Consistent Svarnum evalEnv env addr rtEnv
  Cind : ∀ {m n o : ℕ}{evalEnv : EvalEnv (Fp k) n}
                      {newEvalEnv : Fp k}
                      {env : Env 1 n}
                      {newEnv : Env 1 1}
                      {rtenv newRtenv : RTEnv}
                      (varnum newVarnum : ℕ)
                      -> newVarnum > varnum
                      -> (addr : Vec Addr m)
                      -> (newAddr : Addr)
                      -> Consistent varnum evalEnv env addr rtenv
                      -> rtLookup newAddr (newRtenv Data.List.++ rtenv) ≡ just (Data.Vec.head $ Env.lookup Data.Fin.zero (newEnv Data.Vec.++ env))
                      -> Consistent newVarnum (newEvalEnv ∷ evalEnv) (newEnv Data.Vec.++ env) (newAddr Data.Vec.∷ addr) (newRtenv Data.List.++ rtenv)

fpToVec : {k : ℕ} -> Fp k -> Vec ℕ 1
fpToVec (F x) = x ∷ []

consistent->correct : ∀ {n k : ℕ}
                        {{p : Prime k}}
                        (sp : Compilable.compSize (fpCompilable {k} {p}) ≡ 1)
                        -> (varnum : ℕ)
                        -> (evalEnv : EvalEnv (Fp k) n)
                        -> (env : Env 1 n)
                        -> (addr : Vec Addr 1)
                        -> (rtenv : RTEnv)
                        -> Consistent varnum evalEnv env addr rtenv
                        -> (expr : Expr1 (Fp k) n)
                        -> just (fpToVec $ evalNum' {{numFp {_} {p} {{numℕ}}}} evalEnv expr) ≡
                           runGetResult' (run' {k} {{p}} {{numFp {_} {p} {{numℕ}}}} rtenv (getCompResultIR (fpToIR (varnum , env) expr))) addr
consistent->correct refl varnum evalEnv env addr rtenv consist expr = {!!}

{-
fpVerify' : ∀ {m n : ℕ} {p : Prime n} -> (sp : Compilable.compSize (fpCompilable {n} {p}) ≡ 1)
                                      -> (expr : Expr1 (Fp n) m)
                                      -> EvalEnv (Fp n) m
                                      -> 

consistency : ∀ {m n : ℕ} {p : Prime n} -> (sp : Compilable.compSize (fpCompilable {n} {p} ≡ 1))
                                        -> (expr : Expr1 (Fp n) m)
                                        -> (evalEnv : EvalEnv (FP n) m)
                                        -> (env : Env 1 m)
                                        -> (addr : Vec Addr m)
                                        -> (rtEnv : RTEnv)
                                        -> Consistent evalEnv env addr rtenv
                                        -> fpToIR m
-}

addrMonoInc : {m n o : ℕ}{{p : Prime o}}(env : Env 1 m)(expr : Expr1 (Fp o) m) -> fst (fst (fpToIR {_} {{p}} (n , env) expr)) > n
addrMonoInc {_} {n} {{p}} env (Let1 expr expr₁) = let t = fpToIR {_} {{p}} (suc n , env) expr 
                                                  in ≤-trans (s≤s (≤weak (≤weak (addrMonoInc {n = suc n} env expr)))) (addrMonoInc ((snd (snd t)) ∷ env) expr₁) 
addrMonoInc {m} {n} {o} env (LetC1 (F x) expr) = ≤weak (addrMonoInc ((n ∷ []) ∷ env) expr)
addrMonoInc {suc m} {n} {o} env (Var1 zero) = s≤s ≤-refl
addrMonoInc env (Var1 (suc x)) = s≤s ≤-refl
addrMonoInc {m} {n} {o} {{p}} env (Add1 expr expr₁) = let t = fpToIR (suc n , env) expr
                                                          t1 = fpToIR {o} {{p}} (suc (fst (fst (fpToIR (suc n , env) expr))) , env) expr₁
                                                      in s≤s (≤-trans (≤weak (≤weak (s≤s (s≤s (≤weak (≤weak (addrMonoInc {n = suc n} env expr)))))))
                                                                      (addrMonoInc {n = suc (getCompResultVarnum t)} env expr₁))
addrMonoInc {m} {n} {o} {{p}} env (Mul1 expr expr₁) = let t = fpToIR (suc n , env) expr
                                                          t1 = fpToIR {o} {{p}} (suc (fst (fst (fpToIR (suc n , env) expr))) , env) expr₁
                                                      in s≤s (≤-trans (≤weak (≤weak (s≤s (s≤s (≤weak (≤weak (addrMonoInc {n = suc n} env expr)))))))
                                                                      (addrMonoInc {n = suc (getCompResultVarnum t)} env expr₁))




fpVerify : ∀ {n : ℕ} {p : Prime n} -> (sp : Compilable.compSize (fpCompilable {n} {p}) ≡ 1)
                                   -> (expr : Expr1 (Fp n) 0)
                                   -> just (evalNum {{numFp {_} {p} {{numℕ}}}} expr) ≡ fpRunComp {{p}} {{fpCompilable {n} {p}}} sp expr
fpVerify {n} {p} refl (Let1 expr expr₁) = {!!}
fpVerify refl (LetC1 (F x) expr) = {!!}
fpVerify refl (Var1 ())
fpVerify refl (Add1 expr expr₁) = {!!}
fpVerify refl (Mul1 expr expr₁) = {!!}

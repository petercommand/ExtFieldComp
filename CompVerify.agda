module _ where


open import Data.Nat
open import Data.Nat.Primality
open import Data.Product
open import Data.Maybe
open import MaybeUtil
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


evalNum'->big : ∀ {K : Set} -> {{ins : Num K}}
                            -> {m : ℕ}
                            -> (env : EvalEnv K m)
                            -> (expr : Expr1 K m)
                            -> (r : K)
                            -> evalNum' env expr ≡ r
                            -> ins ∙ env $ expr ↓ r
evalNum'->big {{ins}} env (Let1 expr expr₁) .(evalNum' (evalNum' env expr ∷ env) expr₁) refl =
  let r = evalNum' env expr
  in bigLet1 (evalNum'->big env expr r refl) (evalNum'->big (r ∷ env) expr₁ (evalNum' (r ∷ env) expr₁) refl)
evalNum'->big env (LetC1 x expr) r ev rewrite sym ev = bigLetC1 $ evalNum'->big (x ∷ env) expr (evalNum' (x ∷ env) expr) refl
evalNum'->big env (Var1 x) .(evalLookup x env) refl = bigVar1 x
evalNum'->big env (Add1 expr expr₁) _ refl = bigAdd1 (evalNum'->big env expr (evalNum' env expr) refl) (evalNum'->big env expr₁ (evalNum' env expr₁) refl)
evalNum'->big env (Mul1 expr expr₁) _ refl = bigMul1 (evalNum'->big env expr (evalNum' env expr) refl) (evalNum'->big env expr₁ (evalNum' env expr₁) refl)

big->evalNum' : ∀ {K : Set} -> {{ins : Num K}}
                            -> {m : ℕ}
                            -> (env : EvalEnv K m)
                            -> (expr : Expr1 K m)
                            -> (r : K)
                            -> ins ∙ env $ expr ↓ r
                            -> evalNum' env expr ≡ r
big->evalNum' {_} {{_}} {m} env (Let1 expr expr₁) r (bigLet1 big big₁) rewrite big->evalNum' env expr _ big
                                                                             | big->evalNum' (_ ∷ env) expr₁ r big₁ = refl
big->evalNum' env (LetC1 x expr) r (bigLetC1 big) rewrite big->evalNum' (x ∷ env) expr r big = refl
big->evalNum' env (Var1 n) .(evalLookup n env) (bigVar1 .n) = refl
big->evalNum' env (Add1 expr expr₁) _ (bigAdd1 big big₁) rewrite big->evalNum' env expr _ big
                                                               | big->evalNum' env expr₁ _ big₁ = refl
big->evalNum' env (Mul1 expr expr₁) _ (bigMul1 big big₁) rewrite big->evalNum' env expr _ big
                                                               | big->evalNum' env expr₁ _ big₁ = refl


{-
data Consistent {k : ℕ} {{_ : Prime k}} : {m n : ℕ} -> (varnum : ℕ) -> Env 1 n -> Vec Addr m -> Set where
  Cbase : ∀ {rtenv : RTEnv} -> Consistent 0 [] [] []
  Cinc : ∀ {n : ℕ}{varnum : ℕ} -> (env : Env 1 n)
                               -> (addr : Vec Addr n)
                               -> Consistent varnum env addr
                               -> (Svarnum : ℕ)
                               -> Svarnum > varnum
                               -> Consistent Svarnum env env addr
  Cind : ∀ {m n o : ℕ}{env : Env 1 n}
                      {newEnv : Env 1 1}
                      (varnum newVarnum : ℕ)
                      -> newVarnum > varnum
                      -> (addr : Vec Addr m)
                      -> (newAddr : Addr)
                      -> Consistent varnum env addr
                      -> rtLookup newAddr (newRtenv Data.List.++ rtenv) ≡ just (Data.Vec.head $ Env.lookup Data.Fin.zero (newEnv Data.Vec.++ env))
                      -> Consistent newVarnum (newEnv Data.Vec.++ env) (newAddr Data.Vec.∷ addr) (newRtenv Data.List.++ rtenv)

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



compEq : ∀ {m n varnum : ℕ}{{p : Prime n}}
                           (rtenv : RTEnv)
                           (env : Env 1 m)
                           (expr : Expr1 (Fp n) m)
                           -> let compResult = fpToIR (varnum , env) expr
                              in fpRunWRTEnv {{p}} {{numFp {_} {p} {{numℕ}}}} rtenv (proj₂ compResult) ≡
                                 (maybeComb (fpEnvToEvalEnv {{p}} env rtenv) (\evalEnv -> just (evalNum' {{numFp {_} {p} {{numℕ}}}} evalEnv expr)))
compEq rtenv env (Let1 expr expr₁) = {!!}
compEq {varnum = varnum} rtenv env (LetC1 (F x) expr) = {!compEq {_} {_} {suc varnum} ((varnum , x) ∷ rtenv) ((varnum ∷ []) ∷ env) expr!}
compEq rtenv [] (Var1 ())
compEq rtenv (env ∷ env₁) (Var1 x) = {!!}
compEq rtenv env (Add1 expr expr₁) = {!!}
compEq rtenv env (Mul1 expr expr₁) = {!!}

{-
 compPreserve : ∀ {n : ℕ} {p : Prime n} -> (sp : Compilable.compSize (fpCompilable {n} {p}) ≡ 1)

fpVerify : ∀ {n : ℕ} {p : Prime n} -> (expr : Expr1 (Fp n) 0)
                                   -> just (evalNum {{numFp {_} {p} {{numℕ}}}} expr) ≡ fpRunComp {{p}} {{fpCompilable {n} {p}}} refl expr
fpVerify {n} {p} expr = sym (compEq {{p}} [] [] expr) 
 prove that fpToIR (.varnum , env) (LetC1 (F x) expr) ≡ fpToIR (_varnum_244 env x expr , (x ∷ []) ∷ env) expr
-}

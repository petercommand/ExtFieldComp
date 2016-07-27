module _ where


open import Data.Nat
open import Data.Nat.Primality
open import Data.Product
open import Data.Maybe
open import Data.Vec
open import Data.String
open import Data.List
open import Data.Fin
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



data EnvConsistent : {n : ℕ} -> (env : Env 1 n) -> (rtenv : RTEnv) -> Set where
  envConsistentBase : ∀ {rtenv : RTEnv} -> EnvConsistent [] rtenv
  envConsistentInd : ∀ {n : ℕ}(rtenv' : RTEnv)
                              (env : Env 1  n)
                              (elem : ℕ)
                              -> (rtenv : RTEnv)
                              -> ¬ (rtLookup elem rtenv ≡ nothing)
                              -> EnvConsistent env rtenv'
                              -> EnvConsistent ((elem ∷ []) ∷ env) (rtenv Data.List.++ rtenv')



envConAux : ∀ {m : ℕ} {{p : Prime m}} -> (elem : ℕ) (rtenv : RTEnv) -> ¬ (rtLookup elem rtenv ≡ nothing) -> (rtenv' : RTEnv) -> ¬ (rtLookup elem (rtenv Data.List.++ rtenv') ≡ nothing)
envConAux elem [] x rtenv' x1 = x refl
envConAux elem (x ∷ rtenv) x₁ rtenv' x1 with elem Data.Nat.≟ proj₁ x
envConAux .(proj₁ x) (x ∷ rtenv) x₁ rtenv' x1 | yes refl = x₁ x1
envConAux {m} elem (x ∷ rtenv) x₁ rtenv' x1 | no ¬p = envConAux {m} elem rtenv x₁ _ x1

++-rewrite : ∀ {l}{K : Set l}(a : K)(b : List K)(c : List K) -> a Data.List.∷ b Data.List.++ c ≡ a ∷ (b Data.List.++ c)
++-rewrite a [] c = refl
++-rewrite a (x ∷ b) c = refl

_:>_ : ∀ {l} (K : Set l) (a : K) -> K
a :> b = b

nothing-just : ∀ {K : Set} -> {a : K} -> ¬ (nothing ≡ (Maybe K :> just a))
nothing-just {a} ()

rtLookupShortening : ∀ {elem : ℕ} -> {rtenv rtenv' : RTEnv} -> rtLookup elem (rtenv Data.List.++ rtenv') ≡ nothing -> rtLookup elem rtenv' ≡ nothing
rtLookupShortening {elem} {[]} {rtenv'} p = p
rtLookupShortening {elem} {x ∷ rtenv} {rtenv'} p with elem Data.Nat.≟ proj₁ x
rtLookupShortening .{proj₁ x} {x ∷ rtenv} {rtenv'} p₁ | yes refl = ⊥-elim (nothing-just (sym p₁))
rtLookupShortening {elem} {x ∷ rtenv} {rtenv'} p | no ¬p = rtLookupShortening {elem} {rtenv} {rtenv'} p

rtLookupShortening' : ∀ {elem : ℕ} -> {rtenv rtenv' : RTEnv} -> rtLookup elem (rtenv Data.List.++ rtenv') ≡ nothing -> rtLookup elem rtenv ≡ nothing
rtLookupShortening' {elem} {[]} p = refl
rtLookupShortening' {elem} {x ∷ rtenv} p with elem Data.Nat.≟ proj₁ x
rtLookupShortening' {.(proj₁ x)} {x ∷ rtenv} p₁ | yes refl = ⊥-elim (nothing-just (sym p₁))
rtLookupShortening' {elem} {x ∷ rtenv} {rtenv'} p | no ¬p = rtLookupShortening' {elem} {rtenv} {rtenv'} p
{-
nothingWeakening : ∀ {m n : ℕ} -> {{p : Prime m}} -> (env : Env 1 n) -> (rtenv rtenv' : RTEnv) -> fpEnvToEvalEnv {m} env (rtenv Data.List.++ rtenv') ≡ nothing -> fpEnvToEvalEnv {m} env rtenv' ≡ nothing
nothingWeakening env [] rtenv' p₁ = p₁
nothingWeakening [] (x ∷ rtenv) rtenv' ()
nothingWeakening ((x ∷ []) ∷ env₁) (x₁ ∷ rtenv) rtenv' p₁ with rtLookup x rtenv'
nothingWeakening {m} ((x ∷ []) ∷ env₁) (x₂ ∷ rtenv) rtenv' p₁ | just x₁ with fpEnvToEvalEnv {m} env₁ rtenv'
nothingWeakening ((x₁ ∷ []) ∷ env₁) (x₃ ∷ rtenv) rtenv' p₁ | just x₂ | just x with x₁ Data.Nat.≟ proj₁ x₃
nothingWeakening {m} ((.(proj₁ x₃) ∷ []) ∷ env₁) (x₃ ∷ rtenv) rtenv' p₂ | just x₂ | just x | yes refl = {!!}
nothingWeakening ((x₁ ∷ []) ∷ env₁) (x₃ ∷ rtenv) rtenv' p₁ | just x₂ | just x | no ¬p = {!!}
nothingWeakening ((x ∷ []) ∷ env₁) (x₂ ∷ rtenv) rtenv' p₁ | just x₁ | nothing = {!!}
nothingWeakening ((x ∷ []) ∷ env₁) (x₁ ∷ rtenv) rtenv' p₁ | nothing = refl
-}
fpEnvToEvalEnvWeakening : ∀ {m n : ℕ} {{p : Prime m}} -> (env : Env 1 n)
                                                      -> (rtenv' : RTEnv)
                                                      -> (evalEnv : EvalEnv (Fp m) n)
                                                      -> fpEnvToEvalEnv env rtenv' ≡ just evalEnv
                                                      -> (rtenv : RTEnv)
                                                      -> ¬ (fpEnvToEvalEnv {m} env (rtenv Data.List.++ rtenv') ≡ nothing)
fpEnvToEvalEnvWeakening env rtenv' evalEnv p₁ [] n₁ = ⊥-elim (nothing-just (trans (sym n₁) p₁))
fpEnvToEvalEnvWeakening env rtenv' evalEnv p₁ (x ∷ rtenv) n₁ = {!!}

envConAux' : ∀ {m n : ℕ} {{p : Prime m}} -> (env : Env 1 n)
                                         -> (rtenv' : RTEnv)
                                         -> (evalEnv : EvalEnv (Fp m) n)
                                         -> (fpEnvToEvalEnv {m} env rtenv' ≡ just evalEnv)
                                         -> (rtenv : RTEnv)
                                         -> (Σ (EvalEnv (Fp m) n) (\evalEnv' -> fpEnvToEvalEnv {m} env (rtenv Data.List.++ rtenv') ≡ just evalEnv'))
envConAux' env rtenv' evalEnv p₁ [] = evalEnv , p₁
envConAux' {m} env rtenv' evalEnv p₁ (x ∷ rtenv) with fpEnvToEvalEnv {m} env ((x ∷ rtenv) Data.List.++ rtenv')
envConAux' env rtenv' evalEnv p₁ (x₁ ∷ rtenv) | just x = x , refl
envConAux' env rtenv' evalEnv p₁ (x ∷ rtenv) | nothing = {!!}

rtLookupTotal : (n : ℕ) (rtenv : RTEnv) -> (rtLookup n rtenv ≡ nothing -> ⊥) -> ℕ
rtLookupTotal n rtenv x with rtLookup n rtenv
rtLookupTotal n rtenv x₁ | just x = x
rtLookupTotal n rtenv x | nothing = ⊥-elim (x refl)

----- Every element in a consistent environment is available in the corresponding RTEnv

envConsistent : ∀ {m n : ℕ} {{p : Prime m}} (env : Env 1 n) (rtenv : RTEnv) -> EnvConsistent env rtenv -> (x : ℕ) -> (x ∷ []) ∈ env -> ¬ (rtLookup x rtenv ≡ nothing)
envConsistent .[] rtenv envConsistentBase x () ==nothing
envConsistent .((elem ∷ []) ∷ env) .(rtenv Data.List.++ rtenv') (envConsistentInd rtenv' env elem rtenv x con) .elem here ==nothing = x (rtLookupShortening' {elem} {rtenv} {rtenv'} ==nothing)
envConsistent {m} .((elem ∷ []) ∷ env) .(rtenv Data.List.++ rtenv') (envConsistentInd rtenv' env elem rtenv x con) x₁ (there exist) ==nothing = envConsistent {m} env rtenv' con x₁ exist (rtLookupShortening {x₁} {rtenv} {rtenv'} ==nothing)

-- envConsistent₂ : ∀ {m n : ℕ} {{p : Prime m}} (env : Env 1 n) (rtenv : RTEnv) -> EnvConsistent env rtenv -> 


------- A consistent environment can always be transformed into an EvalEnv
envConsistent' : ∀ {m n : ℕ} {{p : Prime m}} (env : Env 1 n) (rtenv : RTEnv) -> EnvConsistent env rtenv -> Σ (EvalEnv (Fp m) n) (\x -> fpEnvToEvalEnv {m} {_} {{p}} env rtenv ≡ just x)
envConsistent' .[] rtenv envConsistentBase = [] , refl
envConsistent' {m} .((elem ∷ []) ∷ env) .(rtenv Data.List.++ rtenv') (envConsistentInd rtenv' env elem rtenv x con) with envConsistent' {m} env rtenv' con | envConAux {m} elem rtenv x rtenv'
... | (t , t1) | n with rtLookup elem rtenv
envConsistent' {m} .((elem ∷ []) ∷ env) .(rtenv Data.List.++ rtenv') (envConsistentInd rtenv' env elem rtenv x1 con) | t , t1 | n | just x with rtLookup elem (rtenv Data.List.++ rtenv')
envConsistent' {m} .((elem ∷ []) ∷ env) .(rtenv Data.List.++ rtenv') (envConsistentInd rtenv' env elem rtenv x1 con) | t , t1 | n₁ | just x₁ | just x with fpEnvToEvalEnv {m} env (rtenv Data.List.++ rtenv')
envConsistent' .((elem ∷ []) ∷ env) .(rtenv Data.List.++ rtenv') (envConsistentInd rtenv' env elem rtenv x1 con) | t , t1 | n₁ | just x₂ | just x₁ | just x = {!!}
envConsistent' .((elem ∷ []) ∷ env) .(rtenv Data.List.++ rtenv') (envConsistentInd rtenv' env elem rtenv x1 con) | t , t1 | n₁ | just x₁ | just x | nothing = {!!}
envConsistent' .((elem ∷ []) ∷ env) .(rtenv Data.List.++ rtenv') (envConsistentInd rtenv' env elem rtenv x1 con) | t , t1 | n₁ | just x | nothing = ⊥-elim (n₁ refl)
envConsistent' .((elem ∷ []) ∷ env) .(rtenv Data.List.++ rtenv') (envConsistentInd rtenv' env elem rtenv x con) | t , t1 | n | nothing = ⊥-elim (x refl)

-- TBP - A environment generated by comp is always consistent


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

-- compEq' : ∀ {m n varnum : ℕ}{{p : Prime n}}

{-
fpConsistent : {m n : ℕ} (rtenv : RTEnv)
                       (env : Env 1 m)
                       (expr : Expr1 (Fp n) m)
                       {{p : Prime n}}
                       {{ins : Num (Fp n)}}
                       -> (r : Fp n)
                       -> (envc : EnvConsistent env rtenv)
                       -> ins ∙ (fpEnvToEvalEnvTotal {{p}} env rtenv) $ expr ↓ r
-}
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

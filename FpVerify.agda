module _ where

open import Data.Nat
open import Data.Nat.Primality
open import Data.Integer hiding (_≤_; suc)
open import Data.Product
open import Data.Maybe
open import Data.Vec
open import Data.String
open import Data.List
open import Data.Fin hiding (_<_)
open import Data.Empty

open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core

open import RTEnv
open import Env
open import Comp
open import CompVerify
open import FpComp
open import Field
open import Num
open import NatProperties
open import Expr
open import VecAll
open import MaybeUtil

eq' : ∀ {A : Set} (vec : Vec A 1) -> head vec ∷ [] ≡ vec
eq' (x ∷ []) = refl

fpVerify : ∀ {m n : ℕ}{{p : Prime n}}
         (varnum : ℕ)
         (rtenv : RTEnv)
         (evalEnv : EvalEnv (Fp n p) m)
         (env : Env 1 (1 ∷ []) m)
         (cons : EnvConsistent (Fp n p) 1 (1 ∷ [])
           (\x -> fpToInt {n} {{p}} x ∷ [])
           (\x -> F (head x))
           eq'
           evalEnv env rtenv varnum)
         (expr : Expr1 (Fp n p) m)
         -> let varnum1 , ir1 , r1 = fpToIR (varnum , env) expr
            in getBatch r1 (run rtenv ir1) ≡
               fpToInt (evalNum' {{numFp {n} {{p}}}} evalEnv expr)
                 ∷ [] ×
                VecAll (\a -> a < varnum1) r1 ×
                EnvConsistent (Fp n p) 1 (1 ∷ [])
                  (\x -> fpToInt {n} {{p}} x ∷ [])
                  (\x -> F (head x))
                  eq'
                  evalEnv env (run rtenv ir1) varnum1
fpVerify {_} {n} {{p}} varnum rtenv evalEnv env cons (Let1 expr expr₁)
    with fpVerify varnum rtenv evalEnv env cons expr
... | r1↦expr↓ , all1 , cons_r1
    with fpToIR (varnum , env) expr
... | varnum1 , ir1 , r1
    with fpVerify varnum1 (run rtenv ir1)
        (evalNum' {{numFp {n} {{p}}}} evalEnv expr ∷ evalEnv)
        (r1 ∷ env)
        (ConsInd r1↦expr↓ all1 ≤-refl cons_r1)
        expr₁
... | r2↦expr₁↓ , all2 , cons_r2
    with fpToIR (varnum1 , putEnvVal (1 ∷ []) r1 env) expr₁
... | varnum2 , ir2 , r2
    rewrite run-compose ir1 ir2 rtenv
          = r2↦expr₁↓ , all2 , consist-reduce cons_r2
fpVerify varnum rtenv evalEnv env cons (LetC1 (F x) expr)
    with fpVerify (suc varnum) (putRTEnv varnum x rtenv)
          ((F x) ∷ evalEnv) ((varnum ∷ []) ∷ env)
          (ConsInd (cong (\x -> x ∷ [])
             (get-put varnum x rtenv)) (AllI (s≤s ≤-refl) AllB)
                 ≤-refl (consist-inc (rpc-aux ≤-refl ≤-refl cons)
                          (a≤suc-a varnum))) expr
... | r1↦expr↓ , all1 , cons_r1
    with fpToIR (suc varnum , ((varnum ∷ []) ∷ env)) expr
... | varnum1 , ir1 , r1
    = r1↦expr↓ , all1 , consist-reduce cons_r1
fpVerify varnum rtenv evalEnv env cons (Var1 x)
    = consist cons x , consist->vecAll cons x , cons
fpVerify varnum rtenv evalEnv env cons (Add1 expr expr₁)
    with fpVerify varnum rtenv evalEnv env cons expr
... | correct1 , all1 , cons1
    with fpToIR (varnum , env) expr
... | varnum1 , ir1 , r1 ∷ []
    with all1
... | AllI all1' AllB
    with comp-ignorable {_} {1} {1 ∷ []} fpToIR r1 varnum1 all1' {!!} expr₁ env (run rtenv ir1) {!!}
... | ig1
    with fpVerify varnum1 (run rtenv ir1) evalEnv env cons1 expr₁
... | correct2 , all2 , cons2
    with fpToIR (varnum1 , env) expr₁
... | varnum2 , ir2 , r2 ∷ []
    rewrite run-compose ir1 (ir2 Data.List.++
             AddI varnum2 r1 r2 ∷ [])
              rtenv
          | run-compose ir2 (AddI varnum2 r1 r2 ∷ []) (run rtenv ir1)
          | get-put varnum2 (getRTEnv r1 (run (run rtenv ir1) ir2) Data.Integer.+
                             getRTEnv r2 (run (run rtenv ir1) ir2))
                         (run (run rtenv ir1) ir2)
          | cong head correct2
          | ig1
          | cong head correct1
          = cong (λ x → x ∷ []) {!!} , AllI ≤-refl AllB , {!!}
fpVerify varnum rtenv evalEnv env cons (Mul1 expr expr₁) = {!!}

open import Agda.Builtin.Int
open import Data.Nat
open import Data.Nat.Primality
open import Data.Product
open import Data.List hiding (product)
open import Vec as Vec hiding (_++_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Function

open import Comp
open import FpComp
open import Expr
open import Env
open import Field
open import FieldDef
open import RTEnv
open import FpComp
open import Num
open import Expand
open import CompVerify
open import FpVerify hiding (eq')
open import ExtFComp
open import VecAll

eq' : ∀ {m : ℕ}{n}{{p : Prime m}}{vec : Vec ℕ n}
        {n₁ : Vec Int (product vec)}
  ->  (\x -> flatten _ vec (nestMap vec fpToInt x))
           ((\x -> reconstruct _ vec (Vec.map ((Int -> Fp m p) :> F) x)) n₁)
      ≡ n₁
eq' {vec = []} {x ∷ []} = refl
eq' {vec = x ∷ vec} {n₁ = n₁} = {!!}

expandVerify : ∀ {m n o : ℕ}
         -> {{p : Prime m}}
         -> {vec : Vec ℕ n}
         -> (mul : NestF₃ (Fp m p) n vec)
         -> (mul' : NestF₃' (Fp m p) n vec)
         -> (div : NestObj (Fp m p) n vec)
         -> (div' : NestObj' (Fp m p) n vec)
         (evalEnv : EvalEnv (NestMod (Fp m p) n vec) o)
         (expr : Expr1 (NestMod (Fp m p) n vec) o)
         -> let result = flatten _ vec (expand n vec mul div expr)
                evalEnv' = vecExchange (Vec.map (flatten _ vec) evalEnv)
            in reconstruct n vec (Vec.map (\x -> let evalEnv , result = x
                                                 in evalNum' {{numFp {_} {{p}}}} evalEnv result)
                                 (Vec.zip evalEnv' result)) ≡
               extfEval vec mul' div' evalEnv expr
expandVerify {{p}} {vec = []} mul mul' div div' evalEnv (Let1 expr expr₁)
    with expandVerify {vec = []} mul mul' div div' evalEnv expr
... | expandV1
    with expandVerify {vec = []} mul mul' div div' (extfEval [] mul' div' evalEnv expr ∷ evalEnv) expr₁
... | expandV2
    rewrite sym expandV2 = cong (reconstruct 0 [])
                             {Vec.map (λ x → evalNum' {{numFp {_} {{p}}}} (proj₁ x) (proj₂ x))
                              (Vec.zipWith _,_ (vecExchange (Vec.map (λ t → t ∷ []) evalEnv))
                               (Let1 (expand 0 [] mul div expr) (expand 0 [] mul div expr₁) ∷
                                []))}
                             {Vec.map (λ x → evalNum' {{numFp {_} {{p}}}} (proj₁ x) (proj₂ x))
                              (Vec.zipWith _,_
                               (Vec.zipWith _∷_ (extfEval [] mul' div' evalEnv expr ∷ [])
                                (vecExchange (Vec.map (λ t → t ∷ []) evalEnv)))
                               (expand 0 [] mul div expr₁ ∷ []))}
                               {!!}
expandVerify {vec = x ∷ vec} mul mul' div div' evalEnv (Let1 expr expr₁) = {!!}
expandVerify mul mul' div div' evalEnv (LetC1 x expr) = {!!}
expandVerify mul mul' div div' evalEnv (Var1 x) = {!!}
expandVerify mul mul' div div' evalEnv (Add1 expr expr₁) = {!!}
expandVerify {m} {_} {o} {vec = []} mul mul' div div' evalEnv (Mul1 expr expr₁)
    with expandVerify mul mul' div div' evalEnv expr
... | expandV1
    with expandVerify mul mul' div div' evalEnv expr₁
... | expandV2
    with extfEval _ mul' div' evalEnv expr
... | eval1
    with extfEval _ mul' div' evalEnv expr₁
... | eval2
    with vecExchange (Vec.replicate (λ t → t ∷ []) ⊛ evalEnv)
... | test
    = {!!}
expandVerify {vec = x ∷ vec} mul mul' div div' evalEnv (Mul1 expr expr₁)
    with expandVerify mul mul' div div' evalEnv expr
... | expandV1
    with expandVerify mul mul' div div' evalEnv expr₁
... | expandV2
    = {!!}
extfVerify : ∀ {m n o : ℕ}
         -> {{p : Prime m}}
         -> {vec : Vec ℕ n}
         -> (mul : NestF₃ (Fp m p) n vec)
         -> (mul' : NestF₃' (Fp m p) n vec)
         -> (div : NestObj (Fp m p) n vec)
         -> (div' : NestObj' (Fp m p) n vec)
         (varnum : ℕ)
         (rtenv : RTEnv)
         (evalEnv : EvalEnv (NestMod (Fp m p) n vec) o)
         (env : Env n vec o)
         (cons : EnvConsistent (NestMod (Fp m p) n vec) n vec
           (\x -> flatten _ vec (nestMap vec fpToInt x))
           (\x -> reconstruct _ vec (Vec.map F x))
           {!!}
           evalEnv env rtenv varnum)
         (expr : Expr1 (NestMod (Fp m p) n vec) o)
         -> let varnum1 , ir1 , r1 = extfToIR vec mul div (varnum , env) expr
            in nestMap vec ((Int -> Fp m p) :> F)
                 (reconstruct _ vec (getBatch r1 (run rtenv ir1))) ≡
               extfEval vec mul' div' evalEnv expr  ×
                VecAll (\a -> a < varnum1) r1 ×
                EnvConsistent (NestMod (Fp m p) n vec) n vec
                  (\x -> flatten _ vec (nestMap vec fpToInt x))
                  (\x -> reconstruct _ vec (Vec.map F x))
                  {!!}
                  evalEnv env (run rtenv ir1) varnum1
extfVerify mul mul' div div' varnum rtenv evalEnv env cons (Let1 expr expr₁) = {!!}
extfVerify mul mul' div div' varnum rtenv evalEnv env cons (LetC1 x expr) = {!!}
extfVerify mul mul' div div' varnum rtenv evalEnv env cons (Var1 x) = {!!}
extfVerify mul mul' div div' varnum rtenv evalEnv env cons (Add1 expr expr₁) = {!!}
extfVerify mul mul' div div' varnum rtenv evalEnv env cons (Mul1 expr expr₁)
    with extfVerify mul mul' div div' varnum rtenv evalEnv env cons expr
... | correct1 , all1 , cons1
    with extfToIR _ mul div (varnum , env) expr
... | varnum1 , ir1 , r1
    with extfVerify mul mul' div div' varnum1 (run rtenv ir1) evalEnv env cons1 expr₁
... | correct2 , all2 , cons2
    with extfToIR _ mul div (varnum1 , env) expr₁
... | varnum2 , ir2 , r2
    = {!!} , {!!} , {!!}

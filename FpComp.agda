module _ where

open import Data.Nat
open import Data.Maybe
open import Data.Nat.Primality
open import Data.Product
open import Data.List
open import Data.Vec as Vec hiding (_++_)

open import Relation.Binary.PropositionalEquality

open import Function

open import MaybeUtil
open import Comp
open import Expr
open import Env
open import Field
open import RTEnv
open import Num

fpToIR : ∀ {n o : ℕ} {{_ : Prime n}} -> CompState 1 o
                                     -> Expr1 (Fp n) o
                                     -> ℕ × List TAC × Vec Addr 1 -- newVarnum , IR , result address
fpToIR (varnum , env) (Let1 expr expr₁)
    = let varnum1 , ir1 , r1 = fpToIR (varnum , env) expr
          varnum2 , ir2 , r2 = fpToIR (varnum1 , putEnvVal r1 env) expr₁
      in varnum2 , ir1 ++ ir2 , r2
fpToIR (varnum , env) (LetC1 (F x) expr)
    = let varnum1 , ir1 , r1 = fpToIR (suc varnum , putEnvVal (varnum Vec.∷ Vec.[]) env) expr
      in varnum1 , ConstI varnum x ∷ ir1 , r1
fpToIR (varnum , env) (Var1 x) = varnum , [] , Env.lookup x env
fpToIR (varnum , env) (Add1 expr expr₁)
    = let varnum1 , ir1 , r1 = fpToIR (suc varnum , env) expr
          varnum2 , ir2 , r2 = fpToIR (suc varnum1 , env) expr₁
      in suc varnum2 , ir1 ++ ir2 ++ (AddI varnum2 (Vec.head r1) (Vec.head r2) ∷ []) , (varnum2 Vec.∷ Vec.[])
fpToIR (varnum , env) (Mul1 expr expr₁)
    = let varnum1 , ir1 , r1 = fpToIR (suc varnum , env) expr
          varnum2 , ir2 , r2 = fpToIR (suc varnum1 , env) expr₁
      in suc varnum2 , ir1 ++ ir2 ++ (MulI varnum2 (Vec.head r1) (Vec.head r2) ∷ []) , (varnum2 Vec.∷ Vec.[])

fpToVec : ∀ {n} -> Fp n -> Vec ℕ 1
fpToVec (F x) = x ∷ []

fpFromVec : ∀ {n} -> {{_ : Prime n}} -> Vec ℕ 1 -> Fp n
fpFromVec (x ∷ []) = F x

fpToFrom : ∀ {n} -> {{ins : Prime n}} -> ∀ {m} -> fpFromVec {n} {{ins}} (fpToVec m) ≡ m
fpToFrom {m = F x} = refl

fpCompilable : ∀ {n : ℕ} {_ : Prime n} -> Compilable (Fp n)
fpCompilable {_} {p} = record { toIR = fpToIR {_} {_} {{p}}
                              ; compSize = 1
                              ; compToVec = fpToVec
                              ; compFromVec = fpFromVec {_} {{p}}
                              ; compToFrom = fpToFrom {_} {{p}}
                       }

fpRun : ∀ {m} -> {{_ : Prime m}} -> {{num : Num (Fp m)}} -> List TAC × Vec Addr 1 -> Maybe (Fp m)
fpRun {m} {{p}} {{num}} (ir , addr) = maybeComb (run' {{p}} {{num}} [] ir) (\env ->
                                      maybeComb (runGetResult env addr) (\r -> just (F (Vec.head r))))


fpRunWRTEnv : ∀ {m} -> {{_ : Prime m}} -> {{num : Num (Fp m)}} -> RTEnv -> List TAC × Vec Addr 1 -> Maybe (Fp m)
fpRunWRTEnv {m} {{p}} {{num}} rtenv (ir , addr) = maybeComb (run' {{p}} {{num}} rtenv ir) (\env ->
                                                  maybeComb (runGetResult env addr) (\r -> just (F (Vec.head r))))

fpRunComp : ∀ {n : ℕ} {{_ : Prime n}} -> {{ins : Compilable (Fp n)}} -> Compilable.compSize ins ≡ 1 -> Expr1 (Fp n) 0 -> Maybe (Fp n)
fpRunComp {n} {{p}} {{record { toIR = toIR
                             ; compSize = .1
                             ; compToVec = compToVec
                             ; compFromVec = compFromVec
                             ; compToFrom = compToFrom } }} refl expr
   = fpRun {n} {{p}} {{numFp {_} {p} {{numℕ}}}}
           (snd (comp {{record { toIR = toIR
                               ; compSize = 1
                               ; compToVec = compToVec
                               ; compFromVec = compFromVec
                               ; compToFrom = compToFrom } }} expr))


fpRun' : {m : ℕ} -> {{_ : Prime m}} -> {{num : Num (Fp m)}} -> RTEnv -> (List TAC) -> Maybe RTEnv
fpRun' env [] = just env
fpRun' {{p}} {{num}} env (ConstI resAddr val ∷ ir) = fpRun' {{p}} {{num}} (rtInsert (resAddr , val) env) ir
fpRun' {{p}} {{num}} env (AddI x x1 x2 ∷ ir) = case rtLookup x1 env , rtLookup x2 env of
                                          λ { (just val1 , just val2) -> case Num._+_ num (F x1 {{p}}) (F x2 {{p}}) of
                                                                            λ { (F result) -> fpRun' {{p}} {{num}} (rtInsert (x , result) env) ir }
                                            ; (_ , _) -> nothing
                                            }
fpRun' {{p}} {{num}} env (MulI x x1 x2 ∷ ir) = case rtLookup x1 env , rtLookup x2 env of
                                          λ { (just val1 , just val2) -> case Num._*_ num (F x1 {{p}}) (F x2 {{p}}) of
                                                                            λ { (F result) -> fpRun' {{p}} {{num}} (rtInsert (x , result) env) ir }
                                            ; (_ , _) -> nothing
                                            }

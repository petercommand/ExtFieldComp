open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Nat
open import Data.Fin hiding (_+_; _≤_)
import Data.Nat.Properties.Simple as NS
open import Data.Nat.Primality
open import Data.Nat.Show
open import Data.String hiding (_++_)
open import Data.Maybe
open import Data.Product
open import Data.Integer using (ℤ)
open import Data.Bool
open import Data.Vec as Vec hiding (_++_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function

open import Field
open import NatProperties
open import Num
open import Env
open import RTEnv
open import Expr
open import MaybeUtil

module Comp where



record Compilable (A : Set) : Set where
  field
    compSize : ℕ
    toIR : {m : ℕ} -> CompState compSize m -> Expr1 A m -> CompState compSize m × List TAC × Vec ℕ compSize

record Evalable (A : Set) : Set where
  field
    eval : Expr1 A 0 -> A




newVar : ∀ {m n} -> CompState m n -> CompState m n × ℕ
newVar (varnum , env) = ((suc varnum) , env) , varnum

fpToIR : ∀ {n o : ℕ} {{_ : Prime n}} -> CompState 1 o -> Expr1 (Fp n) o -> CompState 1 o × List TAC × Vec Addr 1
fpToIR (varnum , env) (Let1 expr expr₁) with fpToIR (suc varnum , env) expr
... | ((varnum1 , env1) , ir1 , r1) with fpToIR (varnum1 , putEnvVal r1 env) expr₁
... | ((varnum2 , env2) , ir2 , r2) = (varnum2 , env) , ir1 ++ ir2 , r2
fpToIR (varnum , env) (LetC1 (F x) expr) with fpToIR (suc varnum , putEnvVal (varnum Vec.∷ Vec.[]) env) expr
... | ((varnum1 , env1) , ir1 , r1) = ((varnum1 , env) , ConstI varnum x ∷ ir1 , r1)
fpToIR (varnum , env) (Var1 x) = (suc varnum , env) , [] , Env.lookup x env
fpToIR (varnum , env) (Add1 expr expr₁) = let (varnum1 , env1) , ir1 , r1 = fpToIR (suc varnum , env) expr
                                              (varnum2 , env2) , ir2 , r2 = fpToIR (suc varnum1 , env) expr₁
                                          in
                                              (suc varnum2 , env) , ir1 ++ ir2 ++ (AddI varnum2 (Vec.head r1) (Vec.head r2) ∷ []) , (varnum2 Vec.∷ Vec.[])
fpToIR (varnum , env) (Mul1 expr expr₁) = let (varnum1 , env1) , ir1 , r1 = fpToIR (suc varnum , env) expr
                                              (varnum2 , env2) , ir2 , r2 = fpToIR (suc varnum1 , env) expr₁
                                          in
                                              (suc varnum2 , env) , ir1 ++ ir2 ++ (MulI varnum2 (Vec.head r1) (Vec.head r2) ∷ []) , (varnum2 Vec.∷ Vec.[])


fpCompilable : ∀ {n : ℕ} {_ : Prime n} -> Compilable (Fp n)
fpCompilable {_} {p} = record { toIR = fpToIR {_} {_} {{p}}
                              ; compSize = 1
                       }

fst : {A B : Set} -> A × B -> A
fst (a , b) = a

snd : {A B : Set} -> A × B -> B
snd (a , b) = b


data _∙_$_↓_ {K : Set} (num : Num K) : {m : ℕ} -> EvalEnv K m -> Expr1 K m -> K -> Set where
  bigLet1 : ∀ {m} {env : EvalEnv K m} -> {exp : Expr1 K m}
                                      -> {r : K}
                                      -> {exp1 : Expr1 K (suc m)}
                                      -> {r1 : K}
                                      -> num ∙ env $ exp ↓ r
                                      -> num ∙ (r ∷ env) $ exp1 ↓ r1
                                      -> num ∙ env $ Let1 exp exp1 ↓ r1
  bigLetC1 : ∀ {m} {env : EvalEnv K m} -> {const : K}
                                       -> {exp : Expr1 K (suc m)}
                                       -> {r : K}
                                       -> num ∙ (const ∷ env) $ exp ↓ r
                                       -> num ∙ env $ LetC1 const exp ↓ r
  bigVar1 : ∀ {m : ℕ} {env : EvalEnv K m} -> (n : Fin m)
                                      -> num ∙ env $ Var1 n ↓ evalLookup n env
  bigAdd1 : ∀ {m} {env : EvalEnv K m}
                                  -> {exp exp1 : Expr1 K m}
                                  -> {r r1 : K}
                                  -> num ∙ env $ exp ↓ r
                                  -> num ∙ env $ exp1 ↓ r1
                                  -> num ∙ env $ Add1 exp exp1 ↓ Num._+_ num r r1
  bigMul1 : ∀ {m} {env : EvalEnv K m}
                                  -> {exp exp1 : Expr1 K m}
                                  -> {r r1 : K}
                                  -> num ∙ env $ exp ↓ r
                                  -> num ∙ env $ exp1 ↓ r1
                                  -> num ∙ env $ Mul1 exp exp1 ↓ Num._*_ num r r1

evalNum' : ∀ {m : ℕ} {K : Set} -> {{_ : Num K}} -> EvalEnv K m -> Expr1 K m -> K
evalNum' {m} {_} {{num}} env (Let1 expr expr₁) = evalNum' ((evalNum' env expr) Vec.∷ env) expr₁

evalNum' env (LetC1 x₁ expr) = evalNum' (x₁ Vec.∷ env) expr
evalNum' env (Var1 x₁) = evalLookup x₁ env
evalNum' {{num}} env (Add1 expr expr₁) = Num._+_ num (evalNum' env expr) (evalNum' env expr₁)
evalNum' {{num}} env (Mul1 expr expr₁) = Num._*_ num (evalNum' env expr) (evalNum' env expr₁)

evalNum : ∀ {K : Set} -> {{_ : Num K}} -> Expr1 K 0 -> K
evalNum {{num}} expr = evalNum' Vec.[] expr

evalable : ∀ {K : Set} -> {{_ : Num K}} -> Evalable K
evalable {{num}} = record { eval = evalNum {{num}} }

comp : ∀ {A : Set} -> {{ins : Compilable A}} -> Expr1 A 0 -> CompState (Compilable.compSize ins) 0 × List TAC × Vec Addr (Compilable.compSize ins)
comp {{co}} expr = Compilable.toIR co (0 , []) expr


run' : {m : ℕ} -> {{_ : Prime m}} -> {{num : Num (Fp m)}} -> RTEnv -> (List TAC) -> Maybe RTEnv
run' env [] = just env
run' {{p}} {{num}} env (ConstI resAddr val ∷ ir) = run' {{p}} {{num}} (rtInsert (resAddr , val) env) ir
run' {{p}} {{num}} env (AddI x x1 x2 ∷ ir) = case rtLookup x1 env , rtLookup x2 env of
                                          λ { (just val1 , just val2) -> case Num._+_ num (F x1 {{p}}) (F x2 {{p}}) of
                                                                            λ { (F result) -> run' {{p}} {{num}} (rtInsert (x , result) env) ir }
                                            ; (_ , _) -> nothing
                                            }
run' {{p}} {{num}} env (MulI x x1 x2 ∷ ir) = case rtLookup x1 env , rtLookup x2 env of
                                          λ { (just val1 , just val2) -> case Num._*_ num (F x1 {{p}}) (F x2 {{p}}) of
                                                                            λ { (F result) -> run' {{p}} {{num}} (rtInsert (x , result) env) ir }
                                            ; (_ , _) -> nothing
                                            }

runGetResult : {n : ℕ} -> RTEnv -> Vec Addr n -> Maybe (Vec ℕ n)
runGetResult env addr = Vec.foldr (λ x -> Maybe (Vec ℕ x)) (λ x acc → case acc of
                                                     λ { (just acc') -> (case rtLookup x env of
                                                                           (λ { (just result) -> just (Vec._∷_ result acc')
                                                                             ; nothing -> nothing }))
                                                       ; nothing -> nothing
                                                       })  (just Vec.[]) addr

runGetResult' : {n : ℕ} -> Maybe RTEnv -> Vec Addr n -> Maybe (Vec ℕ n)
runGetResult' (just env) addr = Vec.foldr (λ x -> Maybe (Vec ℕ x)) (λ x acc → case acc of
                                                     λ { (just acc') -> (case rtLookup x env of
                                                                           (λ { (just result) -> just (Vec._∷_ result acc')
                                                                             ; nothing -> nothing }))
                                                       ; nothing -> nothing
                                                       })  (just Vec.[]) addr
runGetResult' nothing _ = nothing
fpRun : ∀ {m} -> {{_ : Prime m}} -> {{num : Num (Fp m)}} -> List TAC × Vec Addr 1 -> Maybe (Fp m)
fpRun {m} {{p}} {{num}} (ir , addr) = maybeComb (run' {{p}} {{num}} [] ir) (\env ->
                                      maybeComb (runGetResult env addr) (\r -> just (F (Vec.head r))))


fpRunWRTEnv : ∀ {m} -> {{_ : Prime m}} -> {{num : Num (Fp m)}} -> RTEnv -> List TAC × Vec Addr 1 -> Maybe (Fp m)
fpRunWRTEnv {m} {{p}} {{num}} rtenv (ir , addr) = maybeComb (run' {{p}} {{num}} rtenv ir) (\env ->
                                                  maybeComb (runGetResult env addr) (\r -> just (F (Vec.head r))))

fpRunComp : ∀ {n : ℕ} {{_ : Prime n}} -> {{ins : Compilable (Fp n)}} -> Compilable.compSize ins ≡ 1 -> Expr1 (Fp n) 0 -> Maybe (Fp n)
fpRunComp {n} {{p}} {{record { toIR = toIR ; compSize = .1 }}} refl expr = fpRun {n} {{p}} {{numFp {_} {p} {{numℕ}}}} (snd (comp {{record { toIR = toIR ; compSize = 1 } }} expr))

eval : {A : Set} -> {{_ : Evalable A}} -> Expr1 A 0 -> A
eval {{ev}} expr = Evalable.eval ev expr

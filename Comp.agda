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
module Comp where

Addr : Set
Addr = ℕ

data TAC : Set where
  ConstI : Addr -> ℕ -> TAC
  AddI : Addr -> Addr -> Addr -> TAC
  MulI : Addr -> Addr -> Addr -> TAC

data Expr (A : Set) : Set where
  Const : A → Expr A
  Let : (str : String) -> Expr A -> Expr A -> Expr A
  Var : (str : String) -> Expr A
  Add : Expr A -> Expr A -> Expr A
  Mul : Expr A -> Expr A -> Expr A

data ExprWOConst (A : Set) : Set where
  LetWO : String -> ExprWOConst A -> ExprWOConst A -> ExprWOConst A
  LetWOC : String -> A -> ExprWOConst A -> ExprWOConst A
  VarWO : String -> ExprWOConst A
  AddWO : ExprWOConst A -> ExprWOConst A -> ExprWOConst A
  MulWO : ExprWOConst A -> ExprWOConst A -> ExprWOConst A

data Expr1 (A : Set) : ℕ -> Set where
  Let1 : ∀ {n} -> Expr1 A n -> Expr1 A (suc n) -> Expr1 A n
  LetC1 : ∀ {n} -> A -> Expr1 A (suc n) -> Expr1 A n
  Var1 : ∀ {n} -> Fin n -> Expr1 A n
  Add1 : ∀ {n} -> Expr1 A n -> Expr1 A n -> Expr1 A n
  Mul1 : ∀ {n} -> Expr1 A n -> Expr1 A n -> Expr1 A n

record Compilable (A : Set) : Set where
  field
    compSize : ℕ
    toIR : {m : ℕ} -> CompState compSize m -> Expr1 A m -> CompState compSize m × List TAC × Vec ℕ compSize

record Evalable (A : Set) : Set where
  field
    eval : Expr1 A 0 -> A


newVar : ∀ {m n} -> CompState m n -> CompState m n × ℕ
newVar (varnum , env) = ((suc varnum) , env) , varnum

fpToIR : ∀ {n o : ℕ} {{_ : Prime n}} -> CompState 1 o -> Expr1 (Fp n) o -> CompState 1 o × List TAC × Vec ℕ 1
fpToIR (varnum , env) (Let1 expr expr₁) = case fpToIR (varnum , env) expr of
                                       λ { ((varnum1 , env1) , ir1 , r1) -> case fpToIR (varnum1 , putEnvVal r1 env1) expr₁ of
                                                                            λ { ((varnum2 , env2) , ir2 , r2) -> (varnum2 , env) , ir1 ++ ir2 , r2 }
                                         }
fpToIR (varnum , env) (LetC1 (F x) expr) = case fpToIR (suc varnum , putEnvVal (varnum Vec.∷ Vec.[]) env) expr of
                                              λ { ((varnum1 , env1) , ir1 , r1) -> ((varnum1 , env) , ConstI varnum x ∷ ir1 , r1) }
fpToIR (varnum , env) (Var1 x) = (varnum , env) , [] , Env.lookup x env
fpToIR (varnum , env) (Add1 expr expr₁) = case fpToIR (varnum , env) expr of
                                            λ { ((varnum1 , _) , ir1 , (r1 Vec.∷ Vec.[])) -> case fpToIR (varnum1 , env) expr₁ of
                                                                                   λ { ((varnum2 , _) , ir2 , (r2 Vec.∷ Vec.[])) -> ((suc varnum2 , env) , ir1 ++ ir2 ++ (AddI varnum2 r1 r2 ∷ []) , varnum2 Vec.∷ Vec.[]) }
                                              }
fpToIR (varnum , env) (Mul1 expr expr₁) = case fpToIR (varnum , env) expr of
                                            λ { ((varnum1 , _) , ir1 , (r1 Vec.∷ Vec.[])) -> case fpToIR (varnum1 , env) expr₁ of
                                                                                   λ { ((varnum2 , _) , ir2 , (r2 Vec.∷ Vec.[])) -> ((suc varnum2 , env) , ir1 ++ ir2 ++ (MulI varnum2 r1 r2 ∷ []) , varnum2 Vec.∷ Vec.[]) }
                                              }
                        

fpCompilable : ∀ {n : ℕ} {_ : Prime n} -> Compilable (Fp n)
fpCompilable {_} {p} = record { toIR = fpToIR {_} {_} {{p}}
                              ; compSize = 1
                       }

fst : {A B : Set} -> A × B -> A
fst (a , b) = a

snd : {A B : Set} -> A × B -> B
snd (a , b) = b

evalNum' : ∀ {m : ℕ} {K : Set} -> {{_ : Num K}} -> EvalEnv K m -> Expr1 K m -> K
evalNum' {m} {_} {{num}} env (Let1 expr expr₁) = case evalNum' env expr of
                                                   λ { res -> evalNum' (res Vec.∷ env) expr₁
                                                     }
evalNum' env (LetC1 x₁ expr) = evalNum' (x₁ Vec.∷ env) expr
evalNum' env (Var1 x₁) = evalLookup x₁ env
evalNum' {{num}} env (Add1 expr expr₁) = Num._+_ num (evalNum' env expr) (evalNum' env expr₁)
evalNum' {{num}} env (Mul1 expr expr₁) = Num._*_ num (evalNum' env expr) (evalNum' env expr₁)

evalNum : ∀ {K : Set} -> {{_ : Num K}} -> Expr1 K 0 -> K
evalNum {{num}} expr = evalNum' Vec.[] expr

evalable : ∀ {K : Set} -> {{_ : Num K}} -> Evalable K
evalable {{num}} = record { eval = evalNum {{num}} }

comp : ∀ {m : ℕ}{A : Set} -> {{ins : Compilable A}} -> Expr1 A 0 -> CompState (Compilable.compSize ins) 0 × List TAC × Vec Addr (Compilable.compSize ins)
comp {{co}} expr = Compilable.toIR co (0 , []) expr


run' : {m n : ℕ} -> {{_ : Prime m}} -> {{num : Num (Fp m)}} -> RTEnv -> (List TAC) -> Vec Addr n -> Maybe (Vec ℕ n)
run' env [] addr = Vec.foldr (λ x -> Maybe (Vec ℕ x)) (λ x acc → case acc of
                                                     λ { (just acc') -> (case rtLookup x env of
                                                                           (λ { (just result) -> just (Vec._∷_ result acc')
                                                                             ; nothing -> nothing }))
                                                       ; nothing -> nothing
                                                       })  (just Vec.[]) addr
run' {m} {n} {{p}} {{num}} env (ConstI resAddr val ∷ ir) addr = run' {m} {n} {{p}} {{num}} (rtInsert (resAddr , val) env) ir addr
run' {{p}} {{num}} env (AddI x x1 x2 ∷ ir) addr = case rtLookup x1 env , rtLookup x2 env of
                                          λ { (just val1 , just val2) -> case Num._+_ num (F x1 {{p}}) (F x2 {{p}}) of
                                                                            λ { (F result) -> run' {{p}} {{num}} (rtInsert (x , result) env) ir addr }
                                            ; (_ , _) -> nothing
                                            }
run' {{p}} {{num}} env (MulI x x1 x2 ∷ ir) addr = case rtLookup x1 env , rtLookup x2 env of
                                          λ { (just val1 , just val2) -> case Num._*_ num (F x1 {{p}}) (F x2 {{p}}) of
                                                                            λ { (F result) -> run' {{p}} {{num}} (rtInsert (x , result) env) ir addr }
                                            ; (_ , _) -> nothing
                                            }

fpRun : ∀ {m n} -> {{_ : Prime m}} -> {{num : Num (Fp m)}} -> List TAC × Vec Addr n -> Maybe (Vec ℕ n)
fpRun {m} {n} {{p}} {{num}} (ir , addr) = run' {{p}} {{num}} [] ir addr

fpRunComp : ∀ {n : ℕ} {{_ : Prime n}} -> {{ins : Compilable (Fp n)}} -> Compilable.compSize ins ≡ 1 -> Expr1 (Fp n) 0 -> Maybe (Fp n)
fpRunComp {n} {{p}} {{record { toIR = toIR ; compSize = .1 }}} refl expr = case fpRun {n} {1} {{p}} {{numFp {_} {p} {{numℕ}}}} (snd (comp {n} {{record { toIR = toIR ; compSize = 1 } }} expr)) of
                                                                            λ { (just (x ∷ [])) -> just (F x)
                                                                              ; nothing -> nothing
                                                                              }

eval : {A : Set} -> {{_ : Evalable A}} -> Expr1 A 0 -> A
eval {{ev}} expr = Evalable.eval ev expr

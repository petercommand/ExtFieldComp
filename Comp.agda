open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Nat
open import Data.Integer hiding (_+_; _*_; _≤_)
open import Data.Fin hiding (_+_; _≤_; _<_)
open import Data.Nat.Primality
open import Data.String hiding (_++_)
open import Data.Maybe
open import Data.Product
open import Data.Vec as Vec hiding (_++_)
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
    compOrd : ℕ
    compSize : ℕ
    compTotalSize : ℕ
    compToVec : A -> Vec ℤ compSize
    compFromVec : Vec ℤ compSize -> A
    compToFrom : ∀ {a} -> compFromVec (compToVec a) ≡ a
    compGetConstant : ℕ -> A -> ℕ × List TAC × Vec ℕ compSize
    toIR : {m : ℕ} -> CompState compSize m -> Expr1 A m -> ℕ × List TAC × Vec ℕ compSize

record Evalable (A : Set) : Set where
  field
    eval : ∀ {n} -> EvalEnv A n -> Expr1 A n -> A


newVar : ∀ {m n} -> CompState m n -> CompState m n × ℕ
newVar (varnum , env) = ((ℕ.suc varnum) , env) , varnum


fst : {A B : Set} -> A × B -> A
fst (a , b) = a

snd : {A B : Set} -> A × B -> B
snd (a , b) = b


data _∙_$_↓_ {K : Set} (num : Num K) :
     {m : ℕ} -> EvalEnv K m -> Expr1 K m -> K -> Set where
  bigLet1 : ∀ {m} {env : EvalEnv K m}
      -> {exp : Expr1 K m}
      -> {r : K}
      -> {exp1 : Expr1 K (ℕ.suc m)}
      -> {r1 : K}
      -> num ∙ env $ exp ↓ r
      -> num ∙ (r ∷ env) $ exp1 ↓ r1
      -> num ∙ env $ Let1 exp exp1 ↓ r1
  bigLetC1 : ∀ {m} {env : EvalEnv K m}
      -> {const : K}
      -> {exp : Expr1 K (ℕ.suc m)}
      -> {r : K}
      -> num ∙ (const ∷ env) $ exp ↓ r
      -> num ∙ env $ LetC1 const exp ↓ r
  bigVar1 : ∀ {m : ℕ} {env : EvalEnv K m}
      -> (n : Fin m)
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
evalable {{num}} = record { eval = evalNum' {{num}} }

comp : ∀ {A : Set} -> {{ins : Compilable A}}
                   -> Expr1 A 0
                   -> ℕ × List TAC × Vec Addr (Compilable.compSize ins)
comp {{co}} expr = Compilable.toIR co (0 , []) expr


run : RTEnv -> (List TAC) -> RTEnv
run env [] = env
run env (ConstI resAddr val ∷ ir)
    = run (putRTEnv resAddr val env) ir
run env (AddI x x1 x2 ∷ ir)
    = let val1 = getRTEnv x1 env
          val2 = getRTEnv x2 env
          r = val1 Data.Integer.+ val2
      in run (putRTEnv x r env) ir
run env (SubI x x1 x2 ∷ ir)
    = let val1 = getRTEnv x1 env
          val2 = getRTEnv x2 env
          r = val1 Data.Integer.- val2
      in run (putRTEnv x r env) ir
run env (MulI x x1 x2 ∷ ir)
    = let val1 = getRTEnv x1 env
          val2 = getRTEnv x2 env
          r = val1 Data.Integer.* val2
      in run (putRTEnv x r env) ir

evalTopLevel : {A : Set} -> {{_ : Evalable A}} -> Expr1 A 0 -> A
evalTopLevel {{ev}} expr = Evalable.eval ev Vec.[] expr

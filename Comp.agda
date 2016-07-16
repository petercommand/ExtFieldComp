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
  Let1 : ∀ {m n} -> Expr1 A m -> Expr1 A n -> Expr1 A (suc n)
  LetC1 : ∀ {n} -> A -> Expr1 A n -> Expr1 A n
  Var1 : ∀ {n} -> Fin n -> Expr1 A n
  Add1 : ∀ {m n} -> Expr1 A m -> Expr1 A n -> Expr1 A (max m n)
  Mul1 : ∀ {m n} -> Expr1 A m -> Expr1 A n -> Expr1 A (max m n)


removeConst : ∀ {A} -> Expr A -> ExprWOConst A
removeConst (Const x) = LetWOC "x" x (VarWO "x")
removeConst (Let str expr expr₁) = LetWO str (removeConst expr) (removeConst expr₁)
removeConst (Var str) = VarWO str
removeConst (Add expr expr₁) = AddWO (removeConst expr) (removeConst expr₁)
removeConst (Mul expr expr₁) = MulWO (removeConst expr) (removeConst expr₁)

WOConstVarSize : ∀ {A} -> ExprWOConst A -> ℕ
WOConstVarSize (LetWO x expr expr₁) = 1 + WOConstVarSize expr₁
WOConstVarSize (LetWOC x x₁ expr) = 1 + WOConstVarSize expr
WOConstVarSize (VarWO x) = 0
WOConstVarSize (AddWO expr expr₁) = max (WOConstVarSize expr) (WOConstVarSize expr₁)
WOConstVarSize (MulWO expr expr₁) = max (WOConstVarSize expr) (WOConstVarSize expr₁)

exprWOConstToExpr1 : ∀ {A} -> (expr : ExprWOConst A) -> Expr1 A (WOConstVarSize expr)
exprWOConstToExpr1 (LetWO x expr expr₁) = Let1 (exprWOConstToExpr1 expr) {!exprWOConstToExpr1 expr₁!}
exprWOConstToExpr1 (LetWOC x x₁ expr) = {!!}
exprWOConstToExpr1 (VarWO x) = {!!}
exprWOConstToExpr1 (AddWO expr expr₁) = {!!}
exprWOConstToExpr1 (MulWO expr expr₁) = {!!}

varSize : ∀ {A} -> Expr A -> ℕ
varSize expr = WOConstVarSize (removeConst expr)

record Compilable (A : Set) : Set where
  field
    compSize : ℕ
    preprocess : (expr : Expr A) -> Expr1 A (varSize expr)
    toIR : CompState -> Expr A -> Maybe (CompState × List TAC × Vec ℕ compSize)

record Evalable (A : Set) : Set where
  field
    eval : Expr A -> Maybe A


newVar : CompState -> CompState × ℕ
newVar (varnum , env) = ((suc varnum) , env) , varnum

getConstant : CompState -> ℕ -> CompState × List TAC × Vec ℕ 1
getConstant (varnum , env) num with lookupLen (Data.Nat.Show.show num) 1 env
... | just re = (varnum , env) , [] , re
... | nothing = ((suc varnum) , (((Data.Nat.Show.show num) , varnum ∷ []) ∷ env)) , ConstI varnum num ∷ [] , Vec._∷_ varnum Vec.[]

fpToIR : ∀ {n : ℕ} {_ : Prime n} -> CompState -> Expr (Fp n) -> Maybe (CompState × List TAC × Vec ℕ 1)
fpToIR compState (Const (F x)) = just $ getConstant compState x
fpToIR {_} {p} compState (Let x expr expr1) = let fpToIRRet = fpToIR {_} {p} compState expr
                                                 in case fpToIRRet of
                                                     λ { (just (compState1 , ir1 , r1)) -> 
                                                            case compState1 of
                                                              λ { (varnum , env) -> 
                                                                  let fpToIRRet1 = fpToIR {_} {p} (varnum , putEnvConst (x , Vec.toList r1) env) expr1
                                                                  in case fpToIRRet1 of
                                                                        λ { (just (compState2 , ir2 , r2)) ->
                                                                            case compState2 of
                                                                              λ { (varnum2 , env2) -> just $ (varnum2 , removeEnvConst  (x , Vec.toList r1) env2) , ir1 Data.List.++ ir2 , r2
                                                                                }
                                                                          ; nothing -> nothing
                                                                          }
                                                                }
                                                       ; nothing -> nothing
                                                       }
fpToIR (varnum , env) (Var x) = case lookupLen x 1 env of
                                  λ { (just r) -> just ((varnum , env) , ([] , r))
                                    ; nothing -> nothing
                                    }
fpToIR {_} {p} compState (Add expr expr1) = let
                                                 fpToIRRet1 : _
                                                 fpToIRRet1 = fpToIR {_} {p} compState expr
                                             in case fpToIRRet1 of
                                                  λ { (just (compState1 , ir1 , (Vec._∷_ r1 Vec.[]))) ->
                                                         let fpToIRRet2 = fpToIR {_} {p} compState1 expr1
                                                         in case fpToIRRet2 of
                                                              λ { (just (compState2 , ir2 , (Vec._∷_ r2 Vec.[]))) ->
                                                                     case newVar compState2 of
                                                                           λ { (compState3 , var) -> just (compState3 , ir1 ++ ir2 ++ (AddI var r1 r2 ∷ []) , Vec._∷_ var Vec.[]) }
                                                                ; nothing -> nothing
                                                                }
                                                    ; nothing -> nothing
                                                    }
fpToIR {_} {p} compState (Mul expr expr1) = let
                                                 fpToIRRet1 : _
                                                 fpToIRRet1 = fpToIR {_} {p} compState expr
                                             in case fpToIRRet1 of
                                                  λ { (just (compState1 , ir1 , (Vec._∷_ r1 Vec.[]))) ->
                                                         let fpToIRRet2 = fpToIR {_} {p} compState1 expr1
                                                         in case fpToIRRet2 of
                                                              λ { (just (compState2 , ir2 , (Vec._∷_ r2 Vec.[]))) ->
                                                                     case newVar compState2 of
                                                                           λ { (compState3 , var) -> just (compState3 , ir1 ++ ir2 ++ (MulI var r1 r2 ∷ []) , Vec._∷_ var Vec.[]) }
                                                                ; nothing -> nothing
                                                                }
                                                    ; nothing -> nothing
                                                    }

fpCompilable : ∀ {n : ℕ} {_ : Prime n} -> Compilable (Fp n)
fpCompilable {_} {p} = record { toIR = fpToIR {_} {p}
                              ; compSize = 1  
                       }



evalSubst : ∀ {K : Set} -> String -> K -> Expr K -> Expr K
evalSubst str val (Const x) = Const x
evalSubst str val (Let x exp exp1) with str == x
... | true = Let x exp exp1
... | false = Let x exp (evalSubst str val exp1)
evalSubst str val (Var x) with str == x
... | true = Const val
... | false = Var x
evalSubst str val (Add exp exp1) = Add (evalSubst str val exp) (evalSubst str val exp1)
evalSubst str val (Mul exp exp1) = Mul (evalSubst str val exp) (evalSubst str val exp1)

letSize : ∀ {K : Set} -> Expr K -> ℕ
letSize (Const x) = 1
letSize (Let x expr expr₁) = 1 + letSize expr + letSize expr₁
letSize (Var x) = 1
letSize (Add expr expr₁) = 1 + letSize expr + letSize expr₁
letSize (Mul expr expr₁) = 1 + letSize expr + letSize expr₁

substSize : ∀ {K : Set} -> (s : String) -> (val : K) -> (expr : Expr K) -> (letSize expr ≡ letSize (evalSubst s val expr))
substSize s val (Const x) = refl
substSize s val (Let x expr expr₁) with s == x
... | true = refl
... | false rewrite substSize s val expr₁ = refl
substSize s val (Var x) with s == x
... | true = refl
... | false = refl
substSize s val (Add expr expr₁) rewrite substSize s val expr
                                       | substSize s val expr₁ = refl
substSize s val (Mul expr expr₁) rewrite substSize s val expr
                                       | substSize s val expr₁ = refl

≤-refl : ∀ {a : ℕ} -> a ≤ a
≤-refl {zero} = z≤n
≤-refl {suc a} = s≤s (≤-refl {a})

fst : {A B : Set} -> A × B -> A
fst (a , b) = a

snd : {A B : Set} -> A × B -> B
snd (a , b) = b

lem1 : ∀ {a b : ℕ} -> suc (a + b) > a × suc (a + b) > b
lem1 {zero} {zero} = (s≤s z≤n) , (s≤s z≤n)
lem1 {zero} {suc b} = (s≤s z≤n) , (s≤s (s≤s (≤-refl)))
lem1 {suc a} {zero} rewrite zero-red {a} = (s≤s (s≤s ≤-refl)) , s≤s z≤n
lem1 {suc a} {suc b} rewrite a+suc-b==suc-a+b a b = (s≤s (s≤s (≤weak $ fst $ lem1 {a} {b} ))) , (s≤s (s≤s (≤weak $ snd $ lem1 {a} {b})))


lem3 : ∀ {a b c} -> a ≤ b + c -> a ≤ c + b
lem3 {a} {b} {c} p1 rewrite NS.+-comm b c = p1

evalWithSize : ∀ {K : Set} {{_ : Num K}} {size : ℕ} -> (expr : Expr K) -> (size ≡ letSize expr) -> Acc size -> Maybe K
evalWithSize (Const x) size ac = just x
evalWithSize {_} {{_}} {zero} (Let x expr1 expr2) ()
evalWithSize {K} {{num}} {suc .(letSize expr1 + letSize expr2)} (Let x expr1 expr2) refl (acc ac) = 
               let r1 = evalWithSize {_} {letSize expr1} expr1 refl (ac (letSize expr1) (s≤s (≤-weakening (letSize expr1) (letSize expr1) (letSize expr2) (≤-refl {letSize expr1}))))
               in f r1
                  where
                    f : Maybe K -> Maybe K
                    f (just r1) = evalWithSize
                               {_}
                               {{num}}
                               {letSize expr2}
                               (evalSubst x r1 expr2)
                               (substSize x r1 expr2)
                               (ac (letSize expr2) (s≤s (lem3 {letSize expr2} {letSize expr2} {letSize expr1} $
                                            ≤-weakening (letSize expr2) (letSize expr2) (letSize expr1) (≤-refl {letSize expr2}) )))
                    f nothing = nothing
evalWithSize {_} {{num}} (Var x) size ac = nothing
evalWithSize {K} {{num}} (Add x1 x2) refl (acc ac) =
  let
     r1 : Maybe K
     r1 = evalWithSize x1 refl (ac (letSize x1) (s≤s (≤-weakening (letSize x1) (letSize x1) (letSize x2) $ ≤-refl {letSize x1})))
     r2 : Maybe K
     r2 = evalWithSize x2 refl (ac (letSize x2) ((s≤s (lem3 {letSize x2} {letSize x2} {letSize x1} $ ≤-weakening (letSize x2) (letSize x2) (letSize x1) $ ≤-refl {letSize x2}))))
  in case r1 of λ { (just r11) ->
                          case r2 of λ { (just r22) -> just $ Num._+_ num r11 r22
                                       ; nothing -> nothing } 
                  ; nothing -> nothing }
evalWithSize {K} {{num}} (Mul x1 x2) refl (acc ac) =
  let
     r1 : Maybe K
     r1 = evalWithSize x1 refl (ac (letSize x1) (s≤s (≤-weakening (letSize x1) (letSize x1) (letSize x2) $ ≤-refl {letSize x1})))
     r2 : Maybe K
     r2 = evalWithSize x2 refl (ac (letSize x2) ((s≤s (lem3 {letSize x2} {letSize x2} {letSize x1} $ ≤-weakening (letSize x2) (letSize x2) (letSize x1) $ ≤-refl {letSize x2}))))
  in case r1 of λ { (just r11) ->
                          case r2 of λ { (just r22) -> just $ Num._*_ num r11 r22
                                       ; nothing -> nothing } 
                  ; nothing -> nothing }



evalNum : ∀ {K : Set} -> {{_ : Num K}} -> Expr K -> Maybe K
evalNum {{num}} expr = evalWithSize {_} {{num}} {letSize expr} expr refl (<-wf (letSize expr))

evalable : ∀ {K : Set} -> {{_ : Num K}} -> Evalable K
evalable {{num}} = record { eval = evalNum {{num}} }

comp : ∀ {A : Set} -> {{ins : Compilable A}} -> Expr A -> Maybe (CompState × List TAC × Vec Addr (Compilable.compSize ins))
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

fpRunComp : ∀ {n : ℕ} {{_ : Prime n}} -> {{ins : Compilable (Fp n)}} -> Compilable.compSize ins ≡ 1 -> Expr (Fp n) -> Maybe (Fp n)
fpRunComp {n} {{p}} {{ins}} sp expr with comp {{ins}} expr
... | just (compState , tac , addr) with fpRun {n} {Compilable.compSize ins} {{p}} {{numFp {_} {p} {{numℕ}}}} (tac , addr)
...                                       | just vec with sp
fpRunComp {n} {{x}} {{record { compSize = .1 ; toIR = toIR }}} sp expr | just (compState , tac , addr) | just (Vec._∷_ elem Vec.[]) | refl = just (F elem)
fpRunComp {_} {{p}} {{ins}} sp expr | just (compState , tac , addr) | nothing = nothing
fpRunComp {_} {{p}} {{ins}} sp expr | nothing = nothing

eval : {A : Set} -> {{_ : Evalable A}} -> Expr A -> Maybe A
eval {{ev}} expr = Evalable.eval ev expr

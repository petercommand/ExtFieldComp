module _ where

open import Data.String
open import Data.Nat
open import Data.Fin
open import RTEnv

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

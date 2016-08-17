module _ where

open import Data.Vec
open import Data.String
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Integer hiding (suc; _*_)
open import Data.Fin
open import RTEnv

data TAC : Set where
  ConstI : Addr -> ℤ -> TAC
  AddI : Addr -> Addr -> Addr -> TAC
  SubI : Addr -> Addr -> Addr -> TAC
  MulI : Addr -> Addr -> Addr -> TAC

target : TAC -> Addr
target (ConstI x x₁) = x
target (AddI x x₁ x₂) = x
target (SubI x x₁ x₂) = x
target (MulI x x₁ x₂) = x

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

NestMod : (A : Set) (n : ℕ) -> Vec ℕ n -> Set
NestMod A zero [] = A
NestMod A (suc n) (x ∷ vec) = Vec (NestMod A n vec) x

nestMap : ∀ {A B n} -> (vec : Vec ℕ n) -> (A -> B)
    -> NestMod A n vec -> NestMod B n vec
nestMap [] f x = f x
nestMap (v ∷ vec) f x = Data.Vec.map (nestMap vec f) x

nestZipWith : ∀ {A B C n} -> (vec : Vec ℕ n) -> (A -> B -> C)
    -> NestMod A n vec -> NestMod B n vec
    -> NestMod C n vec
nestZipWith [] f x y = f x y
nestZipWith (v ∷ vec) f x y
    = Data.Vec.map (\x -> nestZipWith vec f (proj₁ x) (proj₂ x))
         (Data.Vec.zip x y)

Op₂ : Set -> Set
Op₂ A = A -> A -> A

Op₃ : Set -> Set
Op₃ A = A -> A -> A -> A

product : ∀ {n} -> Vec ℕ n -> ℕ
product = foldr _ _*_ 1

concat_r : ∀ {A : Set}(a b : ℕ) -> Vec A (a * b) -> Vec (Vec A b) a
concat_r {A} a b vec = proj₁ (group a b vec)

flatten : {A : Set} -> (n : ℕ)(vec : Vec ℕ n)
    -> NestMod A n vec -> Vec A (product vec)
flatten zero [] t = t ∷ []
flatten (suc n) (x ∷ vec) t = concat (map (flatten n vec) t)

reconstruct : {A : Set} -> (n : ℕ)(vec : Vec ℕ n)
     -> Vec A (product vec) -> NestMod A n vec
reconstruct zero [] (x ∷ []) = x
reconstruct (suc n) (x ∷ vec) x₁
    = Data.Vec.map (reconstruct n vec) (concat_r _ _ x₁)

NestF : (A : Set) (n : ℕ) -> Vec ℕ n -> Set
NestF A zero [] = Op₂ A
NestF A (suc n) (x ∷ vec) = (∀ o -> Op₂ (Vec (Expr1 (NestMod A n vec) o) x)) ×
                            NestF A n vec

NestF₃ : (A : Set) (n : ℕ) -> Vec ℕ n -> Set
NestF₃ A zero [] = Op₃ A
NestF₃ A (suc n) (x ∷ vec) = (∀ o -> Op₃ (Vec (Expr1 (NestMod A n vec) o) x)) ×
                            NestF₃ A n vec


NestObj : (A : Set) (n : ℕ) -> Vec ℕ n -> Set
NestObj A zero [] = A
NestObj A (suc n) (x ∷ vec) = (∀ o -> Vec (Expr1 (NestMod A n vec) o) x) ×
                              NestObj A n vec

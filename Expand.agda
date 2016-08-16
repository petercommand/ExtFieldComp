module _ where

open import Data.Nat
open import Data.Vec
open import Data.Product using (_×_; _,_)


open import Expr

NestMod : (A : Set) (n : ℕ) -> Vec ℕ n -> Set
NestMod A zero [] = A
NestMod A (suc n) (x ∷ vec) = Vec (NestMod A n vec) x


Op₂ : Set -> Set
Op₂ A = A -> A -> A

product : ∀ {n} -> Vec ℕ n -> ℕ
product = foldr _ _*_ 1

NestF : (A : Set) (n : ℕ) -> Vec ℕ n -> Set
NestF A zero [] = Op₂ A
NestF A (suc n) (x ∷ vec) = Op₂ (Vec (Expr (NestMod A n vec)) x) × NestF A n vec

NestObj : (A : Set) (n : ℕ) -> Vec ℕ n -> Set
NestObj A zero [] = A
NestObj A (suc n) (x ∷ vec) = Vec (Expr (NestMod A n vec)) x × NestObj A n vec

{-
expandAdd1 : ∀ {A o} (n : ℕ)
   -> (len : ℕ)
   -> (vec : Vec ℕ n)
   -> Expr1 (NestMod A (suc n) (len ∷ vec)) o
   -> Expr1 (NestMod A (suc n) (len ∷ vec)) o
   -> Vec (Expr1 (NestMod A n vec) o) len
expandAdd1 n len vec exp exp₁ = {!!}

-}

expand : ∀ {A o} (n : ℕ)
   -> (vec : Vec ℕ n)
   -> (op : NestF A n vec)
   -> (target : NestObj A n vec)
   -> Expr1 (NestMod A n vec) o
   -> NestMod (Expr1 A o) n vec
expand zero [] _ _ exp = exp
expand (suc n) (x ∷ vec) (op , opᵣ) (target , targetᵣ) (Let1 exp exp₁)
    = {!!}
expand (suc n) (x ∷ vec) (op , opᵣ) (target , targetᵣ) (LetC1 x₁ exp) = {!!}
expand (suc n) (x ∷ vec) (op , opᵣ) (target , targetᵣ) (Var1 x₁) = {!!}
expand (suc n) (x ∷ vec) (op , opᵣ) (target , targetᵣ) (Add1 exp exp₁) = {!!}
expand (suc n) (x ∷ vec) (op , opᵣ) (target , targetᵣ) (Mul1 exp exp₁) = {!!}

expand' : ∀ {A o} (n : ℕ)
    -> (len : ℕ)
    -> (vec : Vec ℕ n)
    -> (op : NestF A n vec)
    -> (target : NestObj A n vec)
    -> Expr1 (NestMod A (suc n) (len ∷ vec)) o
    -> NestMod (Expr1 A o) (suc n) (len ∷ vec) × Vec (Expr1 (NestMod A n vec) o) len
expand' n len vec op target (Let1 expr expr₁) =
  let e , e₁ = expand' n len vec op target expr
      e' , e₁' = expand' n len vec op target expr₁
  in {!!} , {!e₁!}
expand' n len vec op target (LetC1 x expr) = {!!}
expand' n len vec op target (Var1 x) = {!!}
expand' n len vec op target (Add1 expr expr₁) = {!!}
expand' n len vec op target (Mul1 expr expr₁) = {!!}
{-
map (Let1 expr)
 Vec (Expr1 (Vec (NestMod .A n vec) len) (suc .o))
      (_n_102 n len vec op target expr expr₁)
 Vec (Expr1 (NestMod .A n vec) (suc .o)) len

(expand (suc n) (x ∷ vec) (op , opᵣ) (target , targetᵣ) exp₁)
Goal: Vec (NestMod (Expr1 .A o) n vec) x
Have: Vec (NestMod (Expr1 .A (suc o)) n vec) x

(expand (suc n) (x ∷ vec) (op , opᵣ) (target , targetᵣ) exp)
Goal: Vec (NestMod (Expr1 .A .o) n vec) x
Have: Vec (NestMod (Expr1 .A .o) n vec) x
-}

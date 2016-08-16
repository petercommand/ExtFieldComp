module _ where

open import Data.Nat
open import Data.Vec
open import Data.Product using (_×_; _,_; proj₁; proj₂)


open import Comp
open import Env
open import RTEnv
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
NestF A (suc n) (x ∷ vec) = (∀ o -> Op₂ (Vec (Expr1 (NestMod A n vec) o) x)) × NestF A n vec

NestObj : (A : Set) (n : ℕ) -> Vec ℕ n -> Set
NestObj A zero [] = A
NestObj A (suc n) (x ∷ vec) = (∀ o -> Vec (Expr1 (NestMod A n vec) o) x) × NestObj A n vec

expandLet : ∀ {A o} (n : ℕ)
    -> (vec : Vec ℕ n)
    -> NestMod (Expr1 A o) n vec
    -> NestMod (Expr1 A (suc o)) n vec
    -> NestMod (Expr1 A o) n vec
expandLet zero [] e1 e2 = Let1 e1 e2 -- percolate Let to every binder
expandLet (suc n) (x ∷ vec) e1 e2 = zipWith (expandLet n vec) e1 e2

expandLetC : ∀ {A o} (n : ℕ)
    -> (vec : Vec ℕ n)
    -> NestMod A n vec
    -> NestMod (Expr1 A (suc o)) n vec
    -> NestMod (Expr1 A o) n vec
expandLetC zero [] c exp = LetC1 c exp
expandLetC (suc n) (x ∷ vec) c exp = zipWith (expandLetC n vec) c exp

expandAdd : ∀ {A o} (n : ℕ)
    -> (vec : Vec ℕ n)
    -> NestMod (Expr1 A o) n vec
    -> NestMod (Expr1 A o) n vec
    -> NestMod (Expr1 A o) n vec
expandAdd zero [] exp exp₁ = Add1 exp exp₁
expandAdd (suc n) (x ∷ vec) exp exp₁ = zipWith (expandAdd n vec) exp exp₁


expand1 : ∀ {A o} (n : ℕ)
    -> (len : ℕ)
    -> (vec : Vec ℕ n)
    -> (op : NestF A (suc n) (len ∷ vec))
    -> (target : NestObj A (suc n) (len ∷ vec))
    -> Expr1 (NestMod A (suc n) (len ∷ vec)) o
    -> Vec (Expr1 (NestMod A n vec) o) len
expand1 n len vec op target (Let1 exp exp₁)
   = let e1 = expand1 n len vec op target exp
         e2 = expand1 n len vec op target exp₁
     in zipWith Let1 e1 e2
expand1 n len vec op target (LetC1 x exp)
   = let e = expand1 n len vec op target exp
     in zipWith LetC1 x e
expand1 n len vec _ _ (Var1 x) = replicate (Var1 x)
expand1 n len vec op target (Add1 exp exp₁)
   = let e1 = expand1 n len vec op target exp
         e2 = expand1 n len vec op target exp₁
     in zipWith Add1 e1 e2
expand1 {_} {m} n len vec (o , op) (t , target) (Mul1 exp exp₁)
   = let e1 = expand1 n len vec (o , op) (t , target) exp
         e2 = expand1 n len vec (o , op) (t , target) exp₁
     in o m e1 e2 -- something like this, maybe not exactly


expand : ∀ {A o} (n : ℕ)
    -> (vec : Vec ℕ n)
    -> (op : NestF A n vec)
    -> (target : NestObj A n vec)
    -> Expr1 (NestMod A n vec) o
    -> NestMod (Expr1 A o) n vec
expand n vec op target (Let1 expr expr₁)
  = let e = expand n vec op target expr
        e' = expand n vec op target expr₁
    in expandLet n vec e e'
expand n vec op target (LetC1 x expr)
  = let e = expand n vec op target expr
    in expandLetC n vec x e
expand zero [] op target (Var1 x) = Var1 x
expand (suc n) (v ∷ vec) (o , op) (t , target) (Var1 x)
  = replicate (expand n vec op target (Var1 x))
expand zero [] op target (Add1 expr expr₁) = Add1 expr expr₁
expand (suc n) (v ∷ vec) op target (Add1 expr expr₁)
  = let e = expand (suc n) (v ∷ vec) op target expr
        e' = expand (suc n) (v ∷ vec) op target expr₁
    in zipWith (expandAdd n vec) e e'
expand zero [] op target (Mul1 expr expr₁) = Mul1 expr expr₁
expand {_} {m} (suc n) (x ∷ vec) (o , op) (t , target) (Mul1 expr expr₁)
  = let e1 = expand1 n x vec (o , op) (t , target) expr
        e2 = expand1 n x vec (o , op) (t , target) expr₁
    in map (expand n vec op target) (o m e1 e2)


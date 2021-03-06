module _ where

open import Data.Nat
open import Vec
open import Data.Product using (_×_; _,_; proj₁; proj₂)


open import Comp
open import Env
open import RTEnv
open import Expr


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
    -> (op : NestF₂ A (suc n) (len ∷ vec))
--    -> (target : NestObj A (suc n) (len ∷ vec))
    -> Expr1 (NestMod A (suc n) (len ∷ vec)) o
    -> Vec (Expr1 (NestMod A n vec) o) len
expand1 n len vec op (Let1 exp exp₁)
   = let e1 = expand1 n len vec op exp
         e2 = expand1 n len vec op exp₁
     in zipWith Let1 e1 e2
expand1 n len vec op (LetC1 x exp)
   = let e = expand1 n len vec op exp
     in zipWith LetC1 x e
expand1 n len vec _ (Var1 x) = replicate (Var1 x)
expand1 n len vec op (Add1 exp exp₁)
   = let e1 = expand1 n len vec op exp
         e2 = expand1 n len vec op exp₁
     in zipWith Add1 e1 e2
expand1 {_} {m} n len vec (o , op) (Mul1 exp exp₁)
   = let e1 = expand1 n len vec (o , op) exp
         e2 = expand1 n len vec (o , op) exp₁
     in o _ e1 e2


expand : ∀ {A o} (n : ℕ)
    -> (vec : Vec ℕ n)
    -> (mulOp : NestF₂ A n vec)
    -> Expr1 (NestMod A n vec) o
    -> NestMod (Expr1 A o) n vec
expand n vec mul (Let1 expr expr₁)
  = let e = expand n vec mul expr
        e' = expand n vec mul expr₁
    in expandLet n vec e e'
expand n vec mul (LetC1 x expr)
  = let e = expand n vec mul expr
    in expandLetC n vec x e
expand zero [] mul (Var1 x) = Var1 x
expand (suc n) (v ∷ vec) (m , mul) (Var1 x)
  = replicate (expand n vec mul (Var1 x))
expand zero [] mul (Add1 expr expr₁) = Add1 expr expr₁
expand (suc n) (v ∷ vec) mul (Add1 expr expr₁)
  = let e = expand (suc n) (v ∷ vec) mul expr
        e' = expand (suc n) (v ∷ vec) mul expr₁
    in zipWith (expandAdd n vec) e e'
expand zero [] mul (Mul1 expr expr₁) = Mul1 expr expr₁
expand {_} (suc n) (x ∷ vec) (m , mul) (Mul1 expr expr₁)
  = let e1 = expand1 n x vec (m , mul) expr
        e2 = expand1 n x vec (m , mul) expr₁
    in map (expand n vec mul) (m _ e1 e2)


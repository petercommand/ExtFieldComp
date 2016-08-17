module _ where

open import Data.Nat
open import Data.Vec
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
    -> (mulOp : NestF A n vec)
    -> (modOp : NestF A n vec)
    -> (target : NestObj A n vec)
    -> Expr1 (NestMod A n vec) o
    -> NestMod (Expr1 A o) n vec
expand n vec mul mod target (Let1 expr expr₁)
  = let e = expand n vec mul mod target expr
        e' = expand n vec mul mod target expr₁
    in expandLet n vec e e'
expand n vec mul mod target (LetC1 x expr)
  = let e = expand n vec mul mod target expr
    in expandLetC n vec x e
expand zero [] mul mod target (Var1 x) = Var1 x
expand (suc n) (v ∷ vec) (m , mul) (mo , mod) (t , target) (Var1 x)
  = replicate (expand n vec mul mod target (Var1 x))
expand zero [] mul mod target (Add1 expr expr₁) = Add1 expr expr₁
expand (suc n) (v ∷ vec) mul mod target (Add1 expr expr₁)
  = let e = expand (suc n) (v ∷ vec) mul mod target expr
        e' = expand (suc n) (v ∷ vec) mul mod target expr₁
    in zipWith (expandAdd n vec) e e'
expand zero [] mul mod target (Mul1 expr expr₁) = Mul1 expr expr₁
expand {_} (suc n) (x ∷ vec) (m , mul) (mo , mod) (t , target) (Mul1 expr expr₁)
  = let e1 = expand1 n x vec (m , mul) (t , target) expr
        e2 = expand1 n x vec (m , mul) (t , target) expr₁
    in map (expand n vec mul mod target) (mo _ (m _ e1 e2) (t _))


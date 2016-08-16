open import Agda.Builtin.Int
open import Data.Nat
-- open import Data.Integer hiding (suc; _+_; _*_;_≤_)
open import Data.Maybe
open import Data.Nat.Primality
open import Data.Product
open import Data.List hiding (product)
open import Data.Vec as Vec hiding (_++_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Function


open import MaybeUtil
open import Comp
open import Expr
open import Env
open import Field
open import FieldDef
open import RTEnv
open import Num
open import Expand

constFlatMap : ∀ {A : Set} {{comp : Compilable A}}
     -> ℕ -> (list : List A)
     -> ℕ × List TAC × Vec ℕ (length list * Compilable.compSize comp)
constFlatMap varnum [] = varnum , ([] , [])
constFlatMap {{comp}} varnum (x ∷ list) =
  let varnum1 , ir1 , r1 = Compilable.compGetConstant comp varnum x
      varnum2 , ir2 , r2 = constFlatMap {{comp}} varnum1 list
  in varnum2 , (ir1 ++ ir2 , r1 Vec.++ r2)

fillOrTrunc : ∀ {K : Set}{n : ℕ} -> (m : ℕ) -> (def : K) -> Vec K n -> Vec K m
fillOrTrunc zero def _ = []
fillOrTrunc (suc m) def [] = def ∷ fillOrTrunc m def []
fillOrTrunc (suc m) def (x ∷ vec) = x ∷ fillOrTrunc m def vec

{- Abandoned
extfToIR : ∀ {o K x} -> {{compK : Compilable K}}
                     -> CompState (deg x * Compilable.compSize compK) o
                     -> Expr1 (ExtF K x) o
                     -> ℕ × List TAC × Vec Addr (deg x * Compilable.compSize compK)
extfToIR (varnum , env) (Let1 exp exp₁)
   = let varnum1 , ir1 , r1 = extfToIR (varnum , env) exp
         varnum2 , ir2 , r2 = extfToIR (varnum1 , r1 ∷ env) exp₁
     in varnum2 , ir2 , r2
extfToIR {_} {_} {x} {{comp}} (varnum , env) (LetC1 (Ext (P x₁ x₂)) exp)
   = let varnum1 , ir1 , r1 = constFlatMap varnum x₁
     in extfToIR {{comp}} (varnum1 , fillOrTrunc (deg x * Compilable.compSize comp)
                                        0 r1 ∷ env) exp
extfToIR (varnum , env) (Var1 x₁) = varnum , [] , Env.lookup x₁ env
extfToIR {_} {_} {x} {{comp}} (varnum , env) (Add1 exp exp₁)
   = let varnum1 , ir1 , r1 = extfToIR (varnum , env) exp
         varnum2 , ir2 , r2 = extfToIR (varnum1 , env) exp₁
         irs : Vec TAC (deg x * Compilable.compSize comp)
         irs = proj₂ (Vec.foldr (λ x -> ℕ × Vec TAC x)
                 (λ elem acc -> suc (proj₁ acc) ,
                     AddI (proj₁ acc) (proj₁ elem) (proj₂ elem) ∷ proj₂ acc)
                   (varnum2 , []) (Vec.zipWith _,_ r1 r2))
         addrs = Vec.map target irs
     in varnum2 + deg x * Compilable.compSize comp ,
          (ir1 ++ ir2 ++ Vec.toList irs) , addrs
-- This is not correct
extfToIR {_} {_} {x} {{comp}} (varnum , env) (Mul1 exp exp₁)
   = let varnum1 , ir1 , r1 = extfToIR (varnum , env) exp
         varnum2 , ir2 , r2 = extfToIR (varnum1 , env) exp
         irs : Vec TAC (deg x * Compilable.compSize comp)
         irs = proj₂ (Vec.foldr (λ x -> ℕ × Vec TAC x)
                 (λ elem acc -> suc (proj₁ acc) ,
                     MulI (proj₁ acc) (proj₁ elem) (proj₂ elem) ∷ proj₂ acc)
                   (varnum2 , []) (Vec.zipWith _,_ r1 r2))
         addrs = Vec.map target irs
     in varnum2 + deg x * Compilable.compSize comp ,
          (ir1 ++ ir2 ++ Vec.toList irs) , addrs   
-}





extfToIR : ∀ {m n o}
   -> {{p : Prime m}}
   -> (vec : Vec ℕ n)
   -> (div : NestObj (Fp m p) n vec)
   -> CompState (product vec) o
   -> Expr1 (NestMod (Fp m p) n vec) o
   -> ℕ × List TAC × Vec Addr (product vec)
extfToIR vec div (varnum , env) (Let1 exp exp₁)
    = let varnum1 , ir1 , r1 = extfToIR vec div (varnum , env) exp
      in extfToIR vec div (varnum1 , r1 ∷ env) exp₁
extfToIR vec div st (LetC1 x exp) = {!!}
extfToIR vec div (varnum , env) (Var1 x) = varnum , [] , Env.lookup x env
extfToIR vec div st (Add1 exp exp₁) = {!!}
extfToIR vec div st (Mul1 exp exp₁) = {!!}

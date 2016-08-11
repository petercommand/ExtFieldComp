open import Agda.Builtin.Int
open import Data.Nat
-- open import Data.Integer hiding (suc; _+_; _*_;_≤_)
open import Data.Maybe
open import Data.Nat.Primality
open import Data.Product
open import Data.List
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


K2ToIR : ∀ {n} -> {{compK : Compilable K}}
     -> CompState 2 n
     -> Expr1 K2 n
     -> ℕ × List TAC × Vec Addr 2
K2ToIR (varnum , env) (Let1 exp exp₁)
    = let varnum1 , ir1 , r1 = K2ToIR (varnum , env) exp
          varnum2 , ir2 , r2 = K2ToIR (varnum1 , r1 ∷ env) exp₁
      in varnum2 , ir2 , r2
K2ToIR (varnum , env) (LetC1 (Ext (P x₁ x₂)) exp)
    = let varnum1 , ir1 , r1 = constFlatMap varnum x₁
      in K2ToIR (varnum1 , fillOrTrunc 2 0 r1 ∷ env) exp
K2ToIR (varnum , env) (Var1 x) = varnum , [] , Env.lookup x env
K2ToIR (varnum , env) (Add1 exp exp₁)
   = let varnum1 , ir1 , r1 = K2ToIR (varnum , env) exp
         varnum2 , ir2 , r2 = K2ToIR (varnum1 , env) exp₁
         irs : Vec TAC 2
         irs = proj₂ (Vec.foldr (λ x -> ℕ × Vec TAC x)
                 (λ elem acc -> suc (proj₁ acc) ,
                     AddI (proj₁ acc) (proj₁ elem) (proj₂ elem) ∷ proj₂ acc)
                   (varnum2 , []) (Vec.zipWith _,_ r1 r2))
         addrs = Vec.map target irs
     in varnum2 + 2 ,
          (ir1 ++ ir2 ++ Vec.toList irs) , addrs
K2ToIR (varnum , env) (Mul1 exp exp₁) = {!!}

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

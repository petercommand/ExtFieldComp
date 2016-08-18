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


open import Comp
open import FpComp
open import Expr
open import Env
open import Field
open import FieldDef
open import RTEnv
open import FpComp
open import Num
open import Expand


vecExchange : ∀ {A : Set}{a b}
   -> Vec (Vec A a) b
   -> Vec (Vec A b) a
vecExchange [] = Vec.replicate []
vecExchange (vec ∷ vec₁) = let ev = vecExchange vec₁
                            in Vec.zipWith (_∷_) vec ev

extfEvalMul : ∀ {m n}
   -> {{p : Prime m}}
   -> (vec : Vec ℕ n)
   -> (mul : NestF₃' (Fp m p) n vec)
   -> (div : NestObj' (Fp m p) n vec)
   -> NestMod (Fp m p) n vec
   -> NestMod (Fp m p) n vec
   -> NestMod (Fp m p) n vec
extfEvalMul [] mul div r1 r2 = mul r1 r2 div
extfEvalMul (x ∷ vec) (m , _) (d , _) r1 r2 = m r1 r2 d

extfEval : ∀ {m n o}
   -> {{p : Prime m}}
   -> (vec : Vec ℕ n)
   -> (mul : NestF₃' (Fp m p) n vec)
   -> (div : NestObj' (Fp m p) n vec)
   -> EvalEnv (NestMod (Fp m p) n vec) o
   -> Expr1 (NestMod (Fp m p) n vec) o
   -> NestMod (Fp m p) n vec
extfEval vec mul div env (Let1 exp exp₁)
   = let r = extfEval vec mul div env exp
     in extfEval vec mul div (r ∷ env) exp₁
extfEval vec mul div env (LetC1 x exp)
   = extfEval vec mul div (x ∷ env) exp
extfEval vec mul div env (Var1 x) = evalLookup x env
extfEval {m} {{p}} vec mul div env (Add1 exp exp₁)
  = let r1 = extfEval vec mul div env exp
        r2 = extfEval vec mul div env exp₁
        + = Num._+_ (numFp {m} {{p}})
    in nestZipWith vec (+) r1 r2
extfEval {m} {{p}} vec mul div env (Mul1 exp exp₁)
  = let r1 = extfEval vec mul div env exp
        r2 = extfEval vec mul div env exp
    in extfEvalMul vec mul div r1 r2

extfToIR : ∀ {m n o}
   -> {{p : Prime m}}
   -> (vec : Vec ℕ n)
   -> (mul : NestF₃ (Fp m p) n vec)
   -> (div : NestObj (Fp m p) n vec)
   -> CompState n vec o
   -> Expr1 (NestMod (Fp m p) n vec) o
   -> ℕ × List TAC × Vec Addr (product vec)
extfToIR vec mul div (varnum , env) (Let1 exp exp₁)
    = let varnum1 , ir1 , r1 = extfToIR vec mul div (varnum , env) exp
      in extfToIR vec mul div (varnum1 , r1 ∷ env) exp₁
extfToIR vec mul div (varnum , env) (LetC1 x exp)
    = let flat = flatten _ vec x
          varnum1 , ir = Vec.foldr (\n -> ℕ × Vec TAC n) (\elem acc ->
              let varnum' , ir = acc
              in suc varnum' , ConstI varnum' (fpToInt elem) ∷ ir) (varnum , []) flat
      in varnum1 , toList ir , Vec.map target ir
extfToIR vec mul div (varnum , env) (Var1 x)
    = varnum , [] , (Env.lookup vec x env)
extfToIR vec mul div st (Add1 exp exp₁)
    = let varnum1 , ir1 , r1 = extfToIR vec mul div st exp
          varnum2 , ir2 , r2 = extfToIR vec mul div st exp₁
          varnum3 , ir3 = Vec.foldr (λ x -> ℕ × Vec TAC x)
                 (λ elem acc -> suc (proj₁ acc) ,
                     AddI (proj₁ acc) (proj₁ elem) (proj₂ elem) ∷ proj₂ acc)
                   (varnum2 , []) (Vec.zipWith _,_ r1 r2)
          addrs = Vec.map target ir3
      in varnum3 , ir1 ++ ir2 ++ toList ir3 , addrs
extfToIR {_} {n} vec mul div (varnum , env) (Mul1 exp exp₁)
    = let e1 = expand n vec mul div (Mul1 exp exp₁)
          flat = flatten n vec e1
          env' = vecExchange env
          varnum1 , ir , r1 = Vec.foldr (\n -> ℕ × List TAC × Vec Addr n)
             (\elem acc ->
              let varnum' , ir , r = acc
                  fl , en = elem
                  varnum'' , ir1 , r1
                      = fpToIR (varnum , Vec.map (\x -> x ∷ []) en) fl
              in varnum'' , ir1 ++ ir , (head r1) ∷ r) (varnum , [] , [])
                   (Vec.zipWith _,_ flat env')
      in varnum1 , ir , r1


module _ where

open import Data.Nat
open import Data.Maybe
open import Data.Nat.Primality
open import Data.Product
open import Data.List
open import Data.Vec as Vec hiding (_++_)

open import Relation.Binary.PropositionalEquality

open import Function

open import MaybeUtil
open import Comp
open import Expr
open import Env
open import Field
open import RTEnv
open import Num

fpToIR : ∀ {n o : ℕ} {{_ : Prime n}} -> CompState 1 o
                                     -> Expr1 (Fp n) o
                                     -> ℕ × List TAC × Vec Addr 1 -- newVarnum , IR , result address
fpToIR (varnum , env) (Let1 expr expr₁)
    = let varnum1 , ir1 , r1 = fpToIR (varnum , env) expr
          varnum2 , ir2 , r2 = fpToIR (varnum1 , putEnvVal r1 env) expr₁
      in varnum2 , ir1 ++ ir2 , r2
fpToIR (varnum , env) (LetC1 (F x) expr)
    = let varnum1 , ir1 , r1 = fpToIR (suc varnum , putEnvVal (varnum Vec.∷ Vec.[])
                                                          env) expr
      in varnum1 , ConstI varnum x ∷ ir1 , r1
fpToIR (varnum , env) (Var1 x) = varnum , [] , Env.lookup x env
fpToIR (varnum , env) (Add1 expr expr₁)
    = let varnum1 , ir1 , r1 = fpToIR (suc varnum , env) expr
          varnum2 , ir2 , r2 = fpToIR (suc varnum1 , env) expr₁
      in suc varnum2 , ir1 ++ ir2 ++ (AddI varnum2 (Vec.head r1) (Vec.head r2) ∷ [])
                                             , (varnum2 Vec.∷ Vec.[])
fpToIR (varnum , env) (Mul1 expr expr₁)
    = let varnum1 , ir1 , r1 = fpToIR (suc varnum , env) expr
          varnum2 , ir2 , r2 = fpToIR (suc varnum1 , env) expr₁
      in suc varnum2 , ir1 ++ ir2 ++ (MulI varnum2 (Vec.head r1) (Vec.head r2) ∷ [])
                                             , (varnum2 Vec.∷ Vec.[])

fpToVec : ∀ {n} -> Fp n -> Vec ℕ 1
fpToVec (F x) = x ∷ []

fpFromVec : ∀ {n} -> {{_ : Prime n}} -> Vec ℕ 1 -> Fp n
fpFromVec (x ∷ []) = F x

fpToFrom : ∀ {n} -> {{ins : Prime n}}
                 -> ∀ {m} -> fpFromVec {n} {{ins}} (fpToVec m) ≡ m
fpToFrom {m = F x} = refl

fpCompilable : ∀ {n : ℕ} {_ : Prime n} -> Compilable (Fp n)
fpCompilable {_} {p} = record { toIR = fpToIR {_} {_} {{p}}
                              ; compSize = 1
                              ; compToVec = fpToVec
                              ; compFromVec = fpFromVec {_} {{p}}
                              ; compToFrom = fpToFrom {_} {{p}}
                       }

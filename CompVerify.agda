module _ where


open import Data.Nat
open import Data.Nat.Primality
open import Data.Product
open import Data.Maybe
open import Data.Vec
open import Data.String
open import Data.List

open import Relation.Binary.PropositionalEquality

open import RTEnv
open import Env
open import Comp
open import Field
open import Num

open import Function

fpVerify : ∀ {n : ℕ} {p : Prime n} -> (sp : Compilable.compSize (fpCompilable {n} {p}) ≡ 1)
                                   -> (expr : Expr1 (Fp n) 0)
                                   -> just (evalNum {{numFp {_} {p} {{numℕ}}}} expr) ≡ fpRunComp {{p}} {{fpCompilable {n} {p}}} sp expr
fpVerify refl (Let1 expr expr₁) = {!!}
fpVerify refl (LetC1 (F x) expr) = {!!}
fpVerify refl (Var1 ())
fpVerify refl (Add1 expr expr₁) = {!!}
fpVerify refl (Mul1 expr expr₁) = {!!}

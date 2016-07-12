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

fpVerify : ∀ {n : ℕ} {p : Prime n} -> {{compilable : Compilable (Fp n)}}
                                   -> {{evalable : Evalable (Fp n)}}
                                   -> (sp : Compilable.compSize compilable ≡ 1)
                                   -> (expr : Expr (Fp n))
                                   -> eval {{evalable}} expr ≡ fpRunComp {{p}} {{compilable}} sp expr
fpVerify {{compilable = record { compSize = .1 ; toIR = toIR }}} refl (Const x) with toIR (0 , []) (Const x)
fpVerify {n} {p} {{record { compSize = _ ; toIR = toIR }}} refl (Const x) | just (x₁ , proj₁ , proj₂) with fpRun {n} {_} {{p}} {{numFp {_} {p} {{numℕ}}}} (proj₁ , proj₂)
fpVerify {n} {p} {{record { compSize = _ ; toIR = toIR }}} {{evalable}} refl (Const x₂) | just (x₃ , proj₁ , proj₂) | just (x ∷ x₁) with Evalable.eval evalable (Const x₂)
fpVerify {n} {p₁} {{record { compSize = _ ; toIR = toIR }}} refl (Const x₂) | just (x₄ , proj₁ , proj₂) | just (x₁ ∷ x₃) | just (F x) = {!!}
fpVerify {n} {p} {{record { compSize = _ ; toIR = toIR }}} refl (Const x₂) | just (x₃ , proj₁ , proj₂) | just (x ∷ x₁) | nothing = {!!}
fpVerify {n} {p} {{record { compSize = _ ; toIR = toIR }}} refl (Const x) | just (x₁ , proj₁ , proj₂) | nothing = {!!}
fpVerify {n} {p} {{record { compSize = _ ; toIR = toIR }}} refl (Const x) | nothing = {!!}
fpVerify {{compilable = record { compSize = .1 ; toIR = toIR }}} refl (Let str x expr expr₁) = {!!}
fpVerify {{compilable = record { compSize = .1 ; toIR = toIR }}} refl (Var str x) = {!!}
fpVerify {{compilable = record { compSize = .1 ; toIR = toIR }}} refl (Add expr expr₁) = {!!}
fpVerify {{compilable = record { compSize = .1 ; toIR = toIR }}} refl (Mul expr expr₁) = {!!}

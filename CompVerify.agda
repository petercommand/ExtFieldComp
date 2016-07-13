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
fpVerify {n} {p} {{compilable}} {{evalable}} sp expr with Compilable.toIR compilable (0 , []) expr
fpVerify {{compilable}} {{evalable}} sp expr                      | just x with Evalable.eval evalable expr
fpVerify {n} {p} sp expr                                                                       | just (x₁ , x₂) | just (F x) with run' {_} {_} {{p}} {{numFp {n} {p} {{numℕ}}}} [] (proj₁ x₂) (proj₂ x₂)
fpVerify {n} {p} {{record { compSize = .1 ; toIR = toIR }}} {{_}} refl (Const x₃)              | just (x₅ , x₂) | just (F x₄) | just (x ∷ []) = cong (λ x -> just (F x {{p}} )) {!!}
fpVerify {n} {p} {{record { compSize = .1 ; toIR = toIR }}} {{_}} refl (Let str x₃ expr expr₁) | just (x₅ , x₂) | just (F x₄) | just (x ∷ []) = cong (λ x -> just (F x {{p}})) {!!}
fpVerify {n} {p} {{record { compSize = .1 ; toIR = toIR }}} {{_}} refl (Var str x₃)            | just (x₅ , x₂) | just (F x₄) | just (x ∷ []) = cong (λ x -> just (F x {{p}})) {!!}
fpVerify {n} {p} {{record { compSize = .1 ; toIR = toIR }}} {{_}} refl (Add expr expr₁)        | just (x₄ , x₂) | just (F x₃) | just (x ∷ []) = cong (λ x -> just (F x {{p}})) {!!}
fpVerify {n} {p} {{record { compSize = .1 ; toIR = toIR }}} {{_}} refl (Mul expr expr₁)        | just (x₄ , x₂) | just (F x₃) | just (x ∷ []) = cong (λ x -> just (F x {{p}})) {!!}
fpVerify sp expr                                                                               | just (x₁ , x₂) | just (F x)  | nothing = {!!}
fpVerify sp expr                                                  | just (x , x₁)              | nothing = {!!}
fpVerify {n} {p} {{_}} {{evalable}} sp expr                       | nothing with Evalable.eval evalable expr
fpVerify sp expr                                                  | nothing | just x = {!!}
fpVerify sp expr                                                  | nothing | nothing = refl

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
                                   -> (expr : Expr1 (Fp n) 0)
                                   -> just (eval {{evalable}} expr) ≡ fpRunComp {{p}} {{compilable}} sp expr
fpVerify {n} {p} {{compilable = record { compSize = .1 ; toIR = toIR }}} refl expr with fpRun {n} {1} {{p}} {{numFp {_} {p} {{numℕ}}}} (snd (comp {n} {{record { compSize = 1; toIR = toIR}}} expr))
fpVerify {n} {p} {{record { compSize = _ ; toIR = toIR }}} refl expr | just (x ∷ []) = {!!}
fpVerify {n} {p} {{record { compSize = _ ; toIR = toIR }}} refl expr | nothing = {!!}

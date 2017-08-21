module Quotient where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Level

open import Data.Product hiding (map)
open import Data.List
open import Data.Integer renaming (_+_ to _I+_; _-_ to _I-_; _*_ to _I*_) hiding (_≟_)
open import Data.Nat renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)

open import Num
module Quotient (A : Set) (p : List A)
     (num : Num A) (z : A) where
  Poly = List A

  deg : Poly → ℕ
  deg [] = 0
  deg (x ∷ []) = 0
  deg (x ∷ x₁ ∷ p₁) = ℕ.suc (deg (x₁ ∷ p₁))

  open Num.Num
  postulate
    _P/_ : Poly → Poly → Poly
    _P%_ : Poly → Poly → Poly


  _+P_ : Poly → Poly → Poly
  [] +P b = b
  (x ∷ a) +P [] = x ∷ a
  (x ∷ a) +P (x₁ ∷ b) = (_+_ num) x x₁ ∷ a +P b

  _-P_ : Poly → Poly → Poly
  [] -P b = b
  (x ∷ a) -P [] = x ∷ a
  (x ∷ a) -P (x₁ ∷ b) = (_-_ num) x x₁ ∷ a -P b

  _*P_ : Poly → Poly → Poly
  [] *P b = []
  (x ∷ a) *P [] = []
  (x ∷ a) *P (x₁ ∷ b) = (map (_*_ num x) (x₁ ∷ b) +P
                        map (_*_ num x₁) (x ∷ a)) +P
                        (z ∷ a *P b)

  div : (m n : Poly) → ∃₂ λ q r → m ≡ (q *P n) +P r
  div m n = {!!}
  
  data Quotient (p : Poly) : Set where
    ℚ : Poly → Quotient p

  getPoly : ∀ {p} → Quotient p → Poly
  getPoly (ℚ p) = p

  _+ℚ_ : Quotient p → Quotient p → Quotient p
  ℚ x +ℚ ℚ x₁ = ℚ (x +P x₁)
  _-ℚ_ : Quotient p → Quotient p → Quotient p
  ℚ x -ℚ ℚ x₁ = ℚ (x -P x₁)
  _*ℚ_ : Quotient p → Quotient p → Quotient p
  ℚ x *ℚ ℚ x₁ = ℚ (x *P x₁)

  _≈_ : Rel (Quotient p) Level.zero
  _≈_ (ℚ A) (ℚ B) = ∃ λ x → A P% B ≡ map (_*_ num x) p

  _BinPreserves_ : ∀ {a l} {A : Set a} → (A → A → A) → Rel A l → Set _
  _BinPreserves_ _+_ P = _+_ Preserves₂ P ⟶ P ⟶ P

  postulate
    equiv-≈ : IsEquivalence _≈_
    ≈-Preserves+ : _+ℚ_ BinPreserves _≈_
    ≈-Preserves- : _-ℚ_ BinPreserves _≈_
    ≈-Preserves* : _*ℚ_ BinPreserves _≈_

  postulate
    -- normalize quotient to canonical form
    norm : ∀ {p} → Quotient p → Quotient p
    norm-stable : ∀ {p} → (q : Quotient p)
         → norm (norm q) ≡ norm q
    norm-less : ∀ {p} → (q : Quotient p)
         → deg (getPoly (norm q)) < deg p
    

module Quotient where
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Level

open import Data.Product hiding (map)
open import Data.List
open import Data.Nat renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _⊔_ to _ℕ⊔_)


open import Field
open import Num

∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c}
     (D : (x : A) → (y : B x) → (z : C x y) → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
∃₃ C = ∃ λ a → ∃ λ b → ∃ λ c → C a b c

module Quotient (A : Set) (p : List A)
     (num : Num A) (fi : Field A num _≡_) where
  Poly = List A

  deg : Poly → ℕ
  deg [] = 0
  deg (x ∷ []) = 0
  deg (x ∷ x₁ ∷ p₁) = ℕ.suc (deg (x₁ ∷ p₁))

  open Num.Num num
  open Field.Field fi

  +-cancellation : ∀ a b c → a + c ≡ b + c → a ≡ b
  +-cancellation a b c pp with +-inv c
  ... | c⁻¹ , p
      with cong (λ t → t + c⁻¹) pp
  ... | p'
      with +-assoc a c c⁻¹ | +-assoc b c c⁻¹
  ... | r₁ | r₂ with trans r₁ (trans p' (sym r₂))
  ... | r₃ rewrite p | +-id a | +-id b = r₃

  +-ε-mult : ∀ a → (+-ε * a) ≡ +-ε
  +-ε-mult a with +-id +-ε
  ... | p
      with cong (λ t → t * a) p
  ... | p' rewrite right-dist a +-ε +-ε
      with trans p' (sym (+-id (+-ε * a)))
  ... | p'' rewrite +-comm (+-ε * a) +-ε
                  | +-cancellation (+-ε * a) +-ε (+-ε * a) p''
                  = refl

  _+P_ : Poly → Poly → Poly
  [] +P b = b
  (x ∷ a) +P [] = x ∷ a
  (x ∷ a) +P (x₁ ∷ b) = x + x₁ ∷ a +P b

  _-P_ : Poly → Poly → Poly
  [] -P b = b
  (x ∷ a) -P [] = x ∷ a
  (x ∷ a) -P (x₁ ∷ b) = x - x₁ ∷ a -P b

  _*P_ : Poly → Poly → Poly
  [] *P b = []
  (x ∷ a) *P [] = []
  (x ∷ a) *P (x₁ ∷ b) = (map (_*_ x) (x₁ ∷ b) +P
                        map (_*_ x₁) (x ∷ a)) +P
                        (+-ε ∷ a *P b)
  lead : ∀ (n : Poly) → length n > 0 → A
  lead [] ()
  lead (x ∷ n) p₁ = x

  *P-left : ∀ n → length n > 0 → (+-ε ∷ []) *P n ≡ (+-ε ∷ [])
  *P-left [] ()
  *P-left (x ∷ n) p rewrite +-ε-mult x = {!!}

  +-ε-left-+P : ∀ m → ((+-ε ∷ []) +P m) ≡ m
  +-ε-left-+P m = {!!}

  divMod : (m n : Poly)
       → length m > 0 → (p : length n > 0)
       → ¬ (lead n p ≡ +-ε)
       → ∃₂ λ q r → m ≡ (q *P n) +P r
  divMod m n p1 p2 p3
      with deg m | inspect deg m       | deg n | inspect deg n
  ...    | dm    | Reveal_·_is_.[ eq ] | dn    | Reveal_·_is_.[ eq₁ ]
      with compare dm dn
  ... | (less .dm k) rewrite sym eq
                           = +-ε ∷ [] , m ,
                             sym (trans (cong (λ t → t +P m) (*P-left n p2)) (+-ε-left-+P m))
  ... | (equal .dm) = {!!}
  ... | (greater .dn k) = {!!}
{-
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
    
-}

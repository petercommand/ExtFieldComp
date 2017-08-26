{-# OPTIONS --sized-types #-}
module Quotient where
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Level

open import Data.Empty
open import Data.Product hiding (map)
open import Data.List
open import Data.Nat renaming (_+_ to _ℕ+_; _*_ to _ℕ*_; _⊔_ to _ℕ⊔_)

open import NatProperties
open import Field
open import Num

open import Size

data All {A} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

Ahead : ∀ {A P x xs} → All {A} P (x ∷ xs) → P x
Ahead (x₁ ∷ all₁) = x₁

Atail : ∀ {A P x xs} → All {A} P (x ∷ xs) → All P xs
Atail (x₁ ∷ all₁) = all₁

∃₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c}
     (D : (x : A) → (y : B x) → (z : C x y) → Set d) → Set (a ⊔ b ⊔ c ⊔ d)
∃₃ C = ∃ λ a → ∃ λ b → ∃ λ c → C a b c

module Quotient (A : Set) (p : List A)
     (num : AddMul A) (decEq : Decidable (_≡_ {_} {A})) (fi : Field A num _≡_) where


  decAllEq : ∀ a l → Dec (All {A} (_≡_ a) l)
  decAllEq a [] = yes []
  decAllEq a (x ∷ l) with decAllEq a l
  decAllEq a (x ∷ l) | yes p₁ with decEq a x
  decAllEq a (x ∷ l) | yes p₂ | (yes p) = yes (p ∷ p₂)
  decAllEq a (x ∷ l) | yes p₁ | (no ¬p) = no (λ x₁ → ¬p (Ahead x₁))
  decAllEq a (x ∷ l) | no ¬p = no (λ x₁ → ¬p (Atail x₁))

  Poly = List A

  open Num.AddMul num
  open Field.Field fi

  norm-type : Poly → Set
  norm-type [] = Poly
  norm-type (x ∷ []) = Poly
  norm-type (x ∷ x₁ ∷ l) = Dec (All (_≡_ +-ε) (x₁ ∷ l)) → Poly

  norm' : (l : Poly) → norm-type l
  norm' [] = +-ε ∷ []
  norm' (x ∷ []) = x ∷ []
  norm' (x ∷ x₁ ∷ l) (yes p₁) = x ∷ []
  norm' (x ∷ x₁ ∷ []) (no ¬p) = x ∷ x₁ ∷ []
  norm' (x ∷ x₁ ∷ x₂ ∷ l) (no ¬p) = x ∷ norm' (x₁ ∷ x₂ ∷ l) (decAllEq +-ε (x₂ ∷ l))

  norm : Poly → Poly
  norm [] = norm' []
  norm (x ∷ []) = norm' (x ∷ [])
  norm (x ∷ x₁ ∷ l) = norm' (x ∷ x₁ ∷ l) (decAllEq +-ε (x₁ ∷ l))

  norm-stable : ∀ p → norm (norm p) ≡ norm p
  norm-stable [] = refl
  norm-stable (x ∷ []) = refl
  norm-stable (x ∷ x₁ ∷ l) with decAllEq +-ε (x₁ ∷ l)
  norm-stable (x ∷ x₁ ∷ l) | yes p₁ = refl
  norm-stable (x ∷ x₁ ∷ []) | no ¬p with decAllEq +-ε (x₁ ∷ [])
  norm-stable (x ∷ x₁ ∷ []) | no ¬p | (yes p₁) = ⊥-elim (¬p p₁)
  norm-stable (x ∷ x₁ ∷ []) | no ¬p₁ | (no ¬p) = refl
  norm-stable (x₂ ∷ x₁ ∷ x ∷ l) | no ¬p = {!!}
  
  lead' : ∀ (n : Poly) → length n > 0 → A
  lead' [] ()
  lead' (x ∷ []) p₁ = x
  lead' (x ∷ x₁ ∷ n) p₁ = lead' (x₁ ∷ n) (s≤s z≤n)

  norm-len : ∀ n → length n > 0 → length (norm n) > 0
  norm-len [] ()
  norm-len (x ∷ []) (s≤s p₁) = s≤s z≤n
  norm-len (x₁ ∷ x ∷ n) (s≤s p₁) with decAllEq +-ε (x ∷ n)
  norm-len (x₁ ∷ x ∷ n) (s≤s p₂) | yes p₁ = ≤-refl
  norm-len (x₁ ∷ x ∷ []) (s≤s p₁) | no ¬p = s≤s z≤n
  norm-len (x₂ ∷ x₁ ∷ x ∷ n) (s≤s p₁) | no ¬p = s≤s z≤n

  lead : ∀ (n : Poly) → length n > 0 → A
  lead n p = lead' (norm n) (norm-len n p)

  deg' : Poly → ℕ
  deg' [] = 0
  deg' (x ∷ []) = 0
  deg' (x ∷ x₁ ∷ proj₃) = ℕ.suc (deg' (x₁ ∷ proj₃))

  deg : (a : Poly) →  ℕ
  deg p = deg' (norm p)
  
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


  _+P'_ : Poly → Poly → Poly
  [] +P' b = b
  (x ∷ a) +P' [] = x ∷ a
  (x ∷ a) +P' (x₁ ∷ b) = x + x₁ ∷ a +P' b

  _+P_ : Poly → Poly → Poly
  a +P b = norm (a +P' b)

  _-P'_ : Poly → Poly → Poly
  [] -P' b = b
  (x ∷ a) -P' [] = x ∷ a
  (x ∷ a) -P' (x₁ ∷ b) = x + (proj₁ (+-inv x₁)) ∷ a -P' b

  _-P_ : Poly → Poly → Poly
  a -P b = norm (a -P' b)
  
  _*P'_ : Poly → Poly → Poly
  [] *P' b = []
  (x ∷ a) *P' [] = []
  (x ∷ a) *P' (x₁ ∷ b) = (map (_*_ x) (x₁ ∷ b) +P
                        map (_*_ x₁) (x ∷ a)) +P
                        (+-ε ∷ a *P' b)
  _*P_ : Poly → Poly → Poly
  a *P b = norm (a *P' b)

  addMulPoly : AddMul Poly
  addMulPoly = record { _+_ = _+P_ ; _*_ = _*P_ }

  *P-left : ∀ n → length n > 0 → (+-ε ∷ []) *P n ≡ (+-ε ∷ [])
  *P-left [] ()
  *P-left (x ∷ n) p rewrite +-ε-mult x = {!!}

  +-ε-left-+P : ∀ m → ((+-ε ∷ []) +P m) ≡ m
  +-ε-left-+P m = {!!}

  lem-+- : ∀ k m → m ≡ k +P (m -P k)
  lem-+- k m = {!!}

  lem-cancel' : ∀ m n p1 p2
     → deg m ≡ deg n
     → deg m > 0
     → lead m p1 ≡ lead n p2 → deg (m -P n) < deg m
  lem-cancel' [] n () p2 p3 p4 p5
  lem-cancel' (x ∷ m) [] p1 () p3 p4 p5
  lem-cancel' (x ∷ []) (x₁ ∷ []) p1 p2 p3 () p5
  lem-cancel' (x ∷ []) (x₁ ∷ x₂ ∷ n) p1 p2 p3 () p5
  lem-cancel' (x ∷ x₁ ∷ m) (x₂ ∷ []) p1 p2 p3 p4 p5 rewrite p3 with p4
  ... | ()
  lem-cancel' (x ∷ x₁ ∷ m) (x₂ ∷ x₃ ∷ n) (s≤s p1) (s≤s p2) p3 p4 p5 with decAllEq +-ε (x₁ ∷ m) | decAllEq +-ε (x₃ ∷ n)
  lem-cancel' (x ∷ x₁ ∷ m) (x₂ ∷ x₃ ∷ n) (s≤s p1) (s≤s p2) p3 p4 p5 | yes p₁ | (yes p₂) with p4
  ... | ()
  lem-cancel' (x ∷ x₁ ∷ m) (x₂ ∷ x₃ ∷ n) (s≤s p1) (s≤s p2) p3 p4 p5 | yes p₁ | (no ¬p) with p4
  ... | ()
  lem-cancel' (x ∷ x₁ ∷ m) (x₂ ∷ x₃ ∷ n) (s≤s p1) (s≤s p2) p3 p4 p5 | no ¬p | (yes p₁) rewrite p3 with p4
  ... | ()
  lem-cancel' (x ∷ x₁ ∷ m) (x₂ ∷ x₃ ∷ n) (s≤s p1) (s≤s p2) p3 p4 p5 | no ¬p | (no ¬p₁) with decAllEq +-ε ((x₁ + (proj₁ (+-inv x₃))) ∷ (m -P' n))
  lem-cancel' (x ∷ x₁ ∷ m) (x₂ ∷ x₃ ∷ n) (s≤s p1) (s≤s p2) p3 p4 p5 | no ¬p | (no ¬p₁) | yes p' = p4
  lem-cancel' (x ∷ x₁ ∷ m) (x₂ ∷ x₃ ∷ n) (s≤s p1) (s≤s p2) p3 p4 p5 | no ¬p | (no ¬p₁) | no ¬p'
     = {!lem-cancel' (x₁ ∷ m) (x₃ ∷ n)  ? ? ? ? ?!}
  
  lem-cancel : ∀ m n p1 p2 → deg (m -P ((lead m p1 * proj₁ (*-inv (lead n p2)) ∷ []) *P n)) < deg m
  lem-cancel m n p1 p2 with *-inv (lead n p2)
  ... | ln⁻¹ , p = {!!}

  divMod : (m n : Poly)
       → length m > 0 → (p : length n > 0)
       → ¬ (lead n p ≡ +-ε)
       → Acc (deg m)
       → ∃₂ λ q r →
            m ≡ (q *P n) +P r ×
            deg r < deg n ×
            length q > 0 ×
            length r > 0
  divMod m n p1 p2 p3 (acc ac)
      with deg m | inspect deg m       | deg n | inspect deg n
  ...    | dm    | Reveal_·_is_.[ eq ] | dn    | Reveal_·_is_.[ eq₁ ]
      with compare dm dn
  ... | (less .dm k) rewrite sym eq
                           | eq₁
                           = +-ε ∷ [] , m ,
                             sym (trans (cong (λ t → t +P m) (*P-left n p2)) (+-ε-left-+P m)) ,
                             s≤s (≤-weakening (deg m) (deg m) k ≤-refl) ,
                             ≤-refl ,
                             p1
  ... | (equal .dm) = {!!}
  {-
           let
               lm = lead m p1
               ln = lead n p2
               inv = *-inv ln
           in lm * (proj₁ inv) ∷ [] ,
              (m -P ((lm * (proj₁ inv) ∷ []) *P n)) ,
              lem-+- (((lead m p1 * proj₁ (*-inv (lead n p2))) ∷ []) *P n) m ,
              {!!} , ≤-refl , {!!}
  -}
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
  _≈_ (ℚ A) (ℚ B) = ?

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

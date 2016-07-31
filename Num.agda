import Data.Nat
open import Data.Nat.Primality
import Data.Integer
import Data.Sign as Sign
open import Field
open import Function
open import Data.List
-- open import Data.Vec
open Data.Nat hiding (_+_; _*_)
open Data.Integer using (ℤ; _◃_)
open import ListProperties
open import NatProperties
record Num (A : Set) : Set where
  field
    +-id : A
    *-id : A
    _+_ : A -> A -> A
    _*_ : A -> A -> A

numℕ : Num ℕ
numℕ = record {
              _+_ = Data.Nat._+_;
              _*_ = Data.Nat._*_;
              +-id = 0;
              *-id = 1
       }
numℤ : Num ℤ
numℤ = record {
              _+_ = Data.Integer._+_;
              _*_ = Data.Integer._*_;
              +-id = ℤ.pos 0;
              *-id = ℤ.pos 1
       }

private
  _Fp+_ : {n : ℕ} -> {{p : Prime n}} -> {{_ : Num ℕ}} -> Fp n p -> Fp n p -> Fp n p
  _Fp+_ {{_}} {{numℕ}} (F x) (F y) = (F $ (Num._+_ numℕ) x y)

  _Fp*_ : {n : ℕ} -> {{p : Prime n}} -> {{_ : Num ℕ}} -> Fp n p -> Fp n p -> Fp n p
  _Fp*_ {{_}} {{numℕ}} (F x) (F y) = (F $ (Num._*_ numℕ) x y)

numFp : ∀ {n : ℕ}{{p : Prime n}}{{numℕ : Num ℕ}} -> Num (Fp n p)
numFp {_} {{p}} {{numℕ}} = record {
                                _+_ = _Fp+_;
                                _*_ = _Fp*_;
                                +-id = F 0;
                                *-id = F 1
                         }

private
  plus : {K : Set} -> {{num : Num K}} -> List K -> List K -> List K
  plus [] b = b
  plus (x ∷ a) [] = x ∷ a
  plus {{num}} (x ∷ a) (x₁ ∷ b) = Num._+_ num x x₁ ∷ plus a b

  plus>0 : ∀ {K} {{num : Num K}}
                  -> (num1 num2 : List K)
                  -> (length num1 ≥ 0)
                  -> (length num2 > 0)
                  -> length (plus num1 num2) > 0
  plus>0 [] num3 p3 p4 = p4
  plus>0 (x ∷ num3) [] p3 p4 = s≤s z≤n
  plus>0 (x ∷ num3) (x₁ ∷ num4) z≤n (s≤s p4) = s≤s z≤n


  _Poly+_ : {K : Set} -> {{_ : Num K}} -> Poly K -> Poly K -> Poly K
  _Poly+_ {K} {{num}} (P num1 p1) (P num2 p2)
      = P (plus num1 num2) (plus>0 num1 num2 z≤n p2)
       where
  _Poly*_ : {K : Set} -> {{_ : Num K}} -> Poly K -> Poly K -> Poly K
  P [] () Poly* p2
  P (x₁ ∷ x₂) x₃ Poly* P [] ()
  _Poly*_ {K} (P (x₁ ∷ x₂) x₃) (P (x₄ ∷ x₅) x₆)
       = P (mul (x₁ ∷ x₂) (x₄ ∷ x₅)) (mul>0 (x₁ ∷ x₂) (x₄ ∷ x₅) x₃ x₆)
    where
      mul' : {K : Set} -> {{_ : Num K}} -> List K -> K -> List K
      mul' [] elem = []
      mul' {{num}} (x ∷ list) elem = Num._*_ num x elem ∷ mul' list elem

      mul : {K : Set} -> {{_ : Num K}} -> List K -> List K -> List K
      mul [] b = []
      mul (x ∷ a) [] = []
      mul {{num}} (x₁ ∷ a) (x₂ ∷ b)
           = let r1l = mul' a x₂
                 r1 = Num._*_ num x₁ x₂
             in r1 ∷ plus r1l (mul (x₁ ∷ a) b)
      mul'>0 : ∀ {K} {{num : Num K}}
                  -> (num1 : List K)
                  -> length num1 > 0
                  -> (elem : K)
                  -> length (mul' num1 elem) > 0
      mul'>0 [] () elem
      mul'>0 (x₇ ∷ num1) (s≤s p) elem = s≤s z≤n
      mul>0 : ∀ {K} {{num : Num K}}
                   -> (num1 num2 : List K)
                   -> (length num1 > 0)
                   -> (length num2 > 0)
                   -> (length (mul num1 num2) > 0)
      mul>0 [] num2 () p2
      mul>0 (x₇ ∷ num1) [] p1 ()
      mul>0 (x₇ ∷ num1) (x₈ ∷ num2) p1 p2 = s≤s z≤n
numPoly : ∀ {K : Set}{{_ : Num K}} -> Num (Poly K)
numPoly {{num}} = record {
                         _+_ = _Poly+_;
                         _*_ = _Poly*_;
                         +-id = P (Num.+-id num ∷ []) (s≤s z≤n);
                         *-id = P (Num.*-id num ∷ []) (s≤s z≤n)
                  }

_^'_ : ∀ {A : Set} {{_ : Num A}} -> A -> ℕ -> A
_^'_ {{num}} x y = ^-int x y (Num.*-id num)
  where
    ^-int : {A : Set} {{_ : Num A}} -> A -> ℕ -> A -> A
    ^-int x ℕ.zero ac = ac
    ^-int {{num}} x (ℕ.suc y) ac = ^-int x y ((Num._*_ num) ac x)

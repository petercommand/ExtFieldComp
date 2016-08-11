import Data.Nat
open import Data.Nat.Primality
import Data.Integer
import Data.Sign as Sign
open import Field
open import Function
open import Data.List
open import Data.Product
open import Data.Bool
open Data.Nat hiding (_+_; _*_)
open Data.Integer using (ℤ; _◃_)

open import Relation.Binary.PropositionalEquality

open import Frac
open import ListProperties
open import NatProperties
record Num (A : Set) : Set where
  field
    +-id : A
    *-id : A
    _+_ : A -> A -> A
    _-_ : A -> A -> A
    _*_ : A -> A -> A
{-
numℕ : Num ℕ
numℕ = record {
              _+_ = Data.Nat._+_;
              _*_ = Data.Nat._*_;
              +-id = 0;
              *-id = 1
       }

-}

ℕ- : (a b : ℕ) -> a ≥ b -> ℕ
ℕ- a .0 z≤n = a
ℕ- (suc m) (suc n) (s≤s p) = ℕ- m n p
numℤ : Num ℤ
numℤ = record {
              _+_ = Data.Integer._+_;
              _-_ = Data.Integer._-_;
              _*_ = Data.Integer._*_;
              +-id = ℤ.pos 0;
              *-id = ℤ.pos 1
       }

private
  _Fp+_ : {n : ℕ} -> {{p : Prime n}} -> {{_ : Num ℤ}} -> Fp n p -> Fp n p -> Fp n p
  _Fp+_ {{_}} {{numℤ}} (F x) (F y) = (F $ (Num._+_ numℤ) x y)

  _Fp-_ : {n : ℕ} -> {{p : Prime n}} -> {{_ : Num ℤ}} -> Fp n p -> Fp n p -> Fp n p
  _Fp-_ {{_}} {{numℕ}} (F x) (F y) = (F $ (Num._-_ numℤ) x y)

  _Fp*_ : {n : ℕ} -> {{p : Prime n}} -> {{_ : Num ℤ}} -> Fp n p -> Fp n p -> Fp n p
  _Fp*_ {{_}} {{numℤ}} (F x) (F y) = (F $ (Num._*_ numℤ) x y)

numFp : ∀ {n : ℕ} -> {{p : Prime n}} -> Num (Fp n p)
numFp {n} {{p}} = record {
                           _+_ = _Fp+_ {{_}} {{numℤ}};
                           _-_ = _Fp-_ {{_}} {{numℤ}};
                           _*_ = _Fp*_ {{_}} {{numℤ}};
                           +-id = F (ℤ.pos 0);
                           *-id = F (ℤ.pos 1)
                  }
                    

private
  plus : {K : Set} -> {{num : Num K}} -> List K -> List K -> List K
  plus [] b = b
  plus (x ∷ a) [] = x ∷ a
  plus {{num}} (x ∷ a) (x₁ ∷ b) = Num._+_ num x x₁ ∷ plus a b

  minus : {K : Set} -> {{num : Num K}} -> List K -> List K -> List K
  minus a [] = a
  minus {{num}} [] (x ∷ b) = let _-_ = Num._-_ num
                                 +id = Num.+-id num
                             in +id - x ∷ minus [] b
  minus {{num}} (x ∷ a) (x₁ ∷ b) = let _-_ = Num._-_ num
                                   in x - x₁ ∷ minus a b       

  plus>0 : ∀ {K} {{num : Num K}}
                  -> (num1 num2 : List K)
                  -> (length num1 ≥ 0)
                  -> (length num2 > 0)
                  -> length (plus num1 num2) > 0
  plus>0 [] num3 p3 p4 = p4
  plus>0 (x ∷ num3) [] p3 p4 = s≤s z≤n
  plus>0 (x ∷ num3) (x₁ ∷ num4) z≤n (s≤s p4) = s≤s z≤n

  minus>0 : ∀ {K} {{num : Num K}}
                -> (num1 num2 : List K)
                -> length num2 > 0
                -> length (minus num1 num2) > 0
  minus>0 num1 [] ()
  minus>0 [] (x ∷ num2) (s≤s p) = s≤s z≤n
  minus>0 (x ∷ num1) (x₁ ∷ num2) (s≤s p) = s≤s z≤n

  _Poly+_ : {K : Set} -> {{_ : Num K}} -> Poly K -> Poly K -> Poly K
  _Poly+_ {K} {{num}} (P num1 p1) (P num2 p2)
      = P (plus num1 num2) (plus>0 num1 num2 z≤n p2)

  _Poly-_ : {K : Set} -> {{_ : Num K}} -> Poly K -> Poly K -> Poly K
  P num1 p1 Poly- P num2 p2 = P (minus num1 num2) (minus>0 num1 num2 p2)

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
                         _-_ = _Poly-_;
                         _*_ = _Poly*_;
                         +-id = P (Num.+-id num ∷ []) (s≤s z≤n);
                         *-id = P (Num.*-id num ∷ []) (s≤s z≤n)
                  }

-- From http://hackage.haskell.org/package/HaskellForMaths-0.4.8/docs/src/Math-Algebra-Field-Extension.html#ExtensionField
-- Division algorithm

-- leading term
lt : {K : Set} -> Poly K -> K
lt (P x x₁) = last x x₁

lessThan : ℕ -> ℕ -> Bool
lessThan _ zero = false
lessThan zero (suc b) = true
lessThan (suc a) (suc b) = lessThan a b

lessThan' : (a b : ℕ) -> lessThan a b ≡ false -> a ≥ b
lessThan' a zero refl = z≤n
lessThan' zero (suc b) ()
lessThan' (suc a) (suc b) p = s≤s (lessThan' a b p)

monomial : {K : Set} {{_ : Num K}} -> K -> ℕ -> Poly K
monomial {{num}} a i
   = P (replicate i (Num.+-id num) ++ (a ∷ []))
                  (++-length (replicate i (Num.+-id num)) (a ∷ []) z≤n (s≤s z≤n))

{-# TERMINATING #-}
quotRemUP : ∀ {K : Set} {{_ : Num K}} {{poly : Num (Poly K)}} {{_ : Frac K}}
           -> Poly K
           -> Poly K
           -> Poly K × Poly K
quotRemUP {K} {{num}} {{poly}} {{frac}} f g = qr (Num.+-id poly) f
    where
      _+_ = Num._+_ num
      _*_ = Num._*_ num
      _-_ = Num._-_ num
      _P+_ = Num._+_ poly
      _P-_ = Num._-_ poly
      _P*_ = Num._*_ poly
      _ℕ*_ = Data.Nat._*_
      recip = Frac.recip frac
      deg_g = deg g
      lt_g = lt g
      
      qr : Poly K -> Poly K -> Poly K × Poly K
      qr q r
          with lessThan' (deg r) deg_g
      ... | t
          with lessThan (deg r) deg_g
      ... | true = q , r
      ... | false = let s = monomial ((lt r) * recip lt_g) (ℕ- (deg r) deg_g (t refl))
                    in qr (q P+ s) (r P- (s P* g))
modUP : ∀ {K : Set} {{_ : Num K}} {{poly : Num (Poly K)}} {{_ : Frac K}}
           -> Poly K
           -> Poly K
           -> Poly K
modUP f g = proj₂ (quotRemUP f g)


ExtF+ : ∀ {K : Set}{x : Poly K}{{_ : Num (Poly K)}}
      -> ExtF K x -> ExtF K x -> ExtF K x
ExtF+ {{num}} (Ext x) (Ext y) = Ext (Num._+_ num x y)

ExtF- : ∀ {K : Set}{x : Poly K}{{_ : Num (Poly K)}}
      -> ExtF K x -> ExtF K x -> ExtF K x
ExtF- {{num}} (Ext x) (Ext y) = Ext (Num._-_ num x y)

ExtF* : ∀ {K : Set}{x : Poly K}{{_ : Num K}}{{_ : Num (Poly K)}}{{_ : Frac K}}
      -> ExtF K x -> ExtF K x -> ExtF K x
ExtF* {_} {x} {{num}} {{numPoly}} (Ext a) (Ext b)
    = Ext (modUP {{num}} {{numPoly}} (Num._*_ numPoly a b) x)


numExtF : ∀ {K : Set}{x : Poly K}{{_ : Num K}}{{_ : Num (Poly K)}}{{_ : Frac K}} -> Num (ExtF K x)
numExtF {{numK}} {{numPolyK}} {{fracK}}
   = record { +-id = Ext (P (Num.+-id numK  ∷ [])
                                        (s≤s z≤n))
            ; *-id = Ext (P (Num.*-id numK ∷ [])
                          (s≤s z≤n))
            ; _+_ = ExtF+
            ; _-_ = ExtF-
            ; _*_ = ExtF*
            }


_^'_ : ∀ {A : Set} {{_ : Num A}} -> A -> ℕ -> A
_^'_ {{num}} x y = ^-int x y (Num.*-id num)
  where
    ^-int : {A : Set} {{_ : Num A}} -> A -> ℕ -> A -> A
    ^-int x ℕ.zero ac = ac
    ^-int {{num}} x (ℕ.suc y) ac = ^-int x y ((Num._*_ num) ac x)

import Data.Nat
open import Data.Nat.Primality
import Data.Integer
import Data.Sign as Sign
open import Field
open import Function
open import Data.List
open Data.Nat using (ℕ)
open Data.Integer using (ℤ; _◃_)

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
  _Fp+_ : {n : ℕ} -> {{_ : Num ℕ}} -> Fp n -> Fp n -> Fp n
  _Fp+_ {{numℕ}} (F x {{p}}) (F y) = (F $ (Num._+_ numℕ) x y) {{p}}

  _Fp*_ : {n : ℕ} -> {{_ : Num ℕ}} -> Fp n -> Fp n -> Fp n
  _Fp*_ {{numℕ}} (F x {{p}}) (F y) = (F $ (Num._*_ numℕ) x y) {{p}}

numFp : ∀ {n : ℕ}{_ : Prime n}{{numℕ : Num ℕ}} -> Num (Fp n)
numFp {_} {p} {{numℕ}} = record {
                                _+_ = _Fp+_;
                                _*_ = _Fp*_;
                                +-id = F 0 {{p}};
                                *-id = F 1 {{p}}
                         }
private
  _Poly+_ : {K : Set} -> {{_ : Num K}} -> Poly K -> Poly K -> Poly K
  _Poly+_ {{num}} (P []) (P []) = P []
  _Poly+_ {{num}} (P []) (P (y ∷ ys)) = P (y ∷ ys)
  _Poly+_ {{num}} (P (x ∷ xs)) (P []) = P (x ∷ xs)
  _Poly+_ {{num}} (P (x ∷ xs)) (P (y ∷ ys)) =
    let l1 = Num._+_ num x y
        l2 = _Poly+_ (P xs) (P ys)
    in P (l1 ∷ de l2)
       where
         de : {K : Set} -> Poly K -> List K
         de (P m) = m
  _Poly*_ : {K : Set} -> {{_ : Num K}} -> Poly K -> Poly K -> Poly K
  _Poly*_ {{num}} (P []) (P []) = P []
  _Poly*_ {{num}} (P []) (P (y ∷ ys)) = P (y ∷ ys)
  _Poly*_ {{num}} (P (x ∷ xs)) (P []) = P (x ∷ xs)
  _Poly*_ {{num}} (P (x ∷ xs)) (P (y ∷ ys)) =
    let l1 = Num._*_ num x y
        l2 = _Poly*_ (P xs) (P ys)
    in P (l1 ∷ de l2)
       where
         de : {K : Set} -> Poly K -> List K
         de (P m) = m


numPoly : ∀ {K : Set}{{_ : Num K}} -> Num (Poly K)
numPoly {{num}} = record {
                         _+_ = _Poly+_;
                         _*_ = _Poly*_;
                         +-id = P $ Num.+-id num ∷ [];
                         *-id = P $ Num.*-id num ∷ []
                  }

_^_ : ∀ {A : Set} {{_ : Num A}} -> A -> ℕ -> A
_^_ {{num}} x y = ^-int x y (Num.*-id num)
  where
    ^-int : {A : Set} {{_ : Num A}} -> A -> ℕ -> A -> A
    ^-int x ℕ.zero acc = acc
    ^-int {{num}} x (ℕ.suc y) acc = ^-int x y ((Num._*_ num) acc x)


toℤ : ℕ -> ℤ
toℤ = _◃_ Sign.+

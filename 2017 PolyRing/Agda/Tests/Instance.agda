module Tests.Instance where

open import Num
open import Expand

open import Data.Vec
open import Data.Product
import Data.Integer as ℤ
open import Data.Integer using (ℤ)

module Integer where
  instance
    ℤNum : Num ℤ
    Num._+_ ℤNum = ℤ._+_
    Num._-_ ℤNum = ℤ._-_
    Num._*_ ℤNum = ℤ._*_

ℂ : Set → Set
ℂ A = A × A

module Complex (A : Set) {{ins : Num A}} where
  open Num.Num {{...}}
  instance
    ℂNum : ∀ {A} → {{_ : Num A}} → Num (ℂ A)
    Num._+_ ℂNum (x₁ , y₁) (x₂ , y₂) = x₁ + x₂ , y₁ + y₂
    Num._-_ ℂNum (x₁ , y₁) (x₂ , y₂) = x₁ - x₂ , y₁ - y₂
    Num._*_ ℂNum (x₁ , y₁) (x₂ , y₂) = ((x₁ * x₂) - (y₁ * y₂) , (x₁ * y₂) + (y₁ * x₂))

    ℂExtended : Extended ℂ 2
    Extended.fromVec ℂExtended (x ∷ y ∷ []) = x , y
    Extended.toVec ℂExtended (x , y) = x ∷ y ∷ []

    ℂFunctor : Functor ℂ
    Functor.fmap ℂFunctor f (x , y) = f x , f y

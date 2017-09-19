module ExpandTest where

open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Vec
open import Num
open import PolyRing renaming (fmap to Pfmap)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties.Simple

{- descInds 3 = (Lit . Lit $ Ind) ∷ Lit Ind ∷ Ind ∷ []
   decs stands for "descending". -}
descInds : ∀ {A : Set} n → Vec (ExprN A n) n
descInds n = desc n n
  where lits : ∀ {A : Set} n k → ExprN A n
        lits n zero = {! Ind  !}
        lits n (suc k) = {!   !}

        desc : ∀ {A : Set} n k → Vec (ExprN A n) k
        desc n zero = []
        desc n (suc k) = lits n k ∷ desc n k


expand : ∀ {A} n
  → {{num : Num A}}
  → {{numE : Num (Vec (ExprN A n) n)}}
  → Expr (Vec A n) → Vec (ExprN A n) n
expand n = foldExpr (descInds n) (map (liftExpr (≤→≤′ 0 n z≤n)))

toNest : ∀ {A} n → Vec A n → Nest A n
toNest zero _ = tt
toNest (suc n) (x ∷ xs) = liftVal n x , toNest n xs


private
 refl-Ind : ∀ {A n} → {{num : Num A}} → (xs : Vec A n)
          → xs ≡ map (λ e → semantics n e (toNest n xs)) (descInds n)
 refl-Ind [] = refl
 refl-Ind (x ∷ []) = refl
 refl-Ind (x ∷ y ∷ xs) = {!   !}

expand-correct : ∀ {A n}
  → {{num : Num A}}
  → {{numV : Num (Vec A n)}}
  → {{numE : Num (Vec (ExprN A n) n)}}
  → (e : Expr (Vec A n)) → (xs : Vec A n)
  → semantics1 e xs ≡ map (λ e → semantics n e (toNest n xs)) (expand n e)
expand-correct Ind xs = refl-Ind xs
expand-correct (Lit x) xs = {!   !}
expand-correct (Add e e₁) xs = {!   !}
expand-correct (Sub e e₁) xs = {!   !}
expand-correct (Mul e e₁) xs = {!   !}

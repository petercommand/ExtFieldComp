module ExpandTest where

open import Data.Unit using (⊤; tt)
open import Data.Product hiding (map)
open import Function using (_∘_)
open import Data.Nat
open import Data.Vec hiding (map)
open import Num
open import PolyRing renaming (fmap to Pfmap)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties.Simple

{- The built-in map is defined in terms of replicate and _⊛_,
   for its own reason. For our context, the "traditional" definition
   below allows us to work in a more abstract level. -}

map : ∀ {l} {A B : Set l} {n} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

postulate
  map-compose : ∀ {l} {n : ℕ} {A B C : Set l}
    → (f : B → C) → (g : A → B) → (xs : Vec A n)
    → map f (map g xs) ≡ map (f ∘ g) xs

  map-cong : ∀ {l} {n : ℕ} {A B : Set l}
      → (f g : A → B) → (∀ x → f x ≡ g x)
      → (xs : Vec A n)
      → map f xs ≡ map g xs

  map-id : ∀ {l} {n : ℕ} {A : Set l}
      → (xs : Vec A n)
      → map (λ x → x) xs ≡ xs

genInd : ∀ {A : Set} (n : ℕ) → Vec (ExprN A n) n
genInd zero = []
genInd (suc zero) = Ind ∷ []
genInd (suc (suc n)) = Ind ∷ (map Lit (genInd (suc n)))

expand : ∀ {A} n
  → {{numE : Num (Vec (ExprN A n) n)}}
  → Expr (Vec A n) → Vec (ExprN A n) n
expand n = foldExpr (genInd n) (map (liftVal n))

toNest : ∀ {A} n → Vec A n → Nest A n
toNest zero _ = tt
toNest (suc n) (x ∷ xs) = liftVal n x , toNest n xs

private
 sem-lift-cancel : ∀ {A} n {{num : Num A}}
     → (xs : Nest A n) → (x : A)
     → semantics n (liftVal n x) xs ≡ x
 sem-lift-cancel zero xs x = refl
 sem-lift-cancel (suc n) xs x = sem-lift-cancel n (proj₂ xs) x

 refl-Ind : ∀ {A n} → {{num : Num A}} → (xs : Vec A n)
          → xs ≡ map (λ e → semantics n e (toNest n xs)) (genInd n)
 refl-Ind [] = refl
 refl-Ind (x ∷ []) = refl
 refl-Ind {n = suc (suc n)} (x ∷ y ∷ xs)
   rewrite sem-lift-cancel n (toNest n xs) x
         | map-compose (λ e → semantics _ e (toNest _ (x ∷ y ∷ xs)))
                       Lit (genInd (suc n))
         | refl-Ind (y ∷ xs)
   = refl

numV-natural : (∀ {A : Set} → Num A → ∀ {n} → Num (Vec A n)) → Set₁
numV-natural toNumV =
   ∀ {A B : Set} (trans : A → B) (num₁ : Num A) (num₂ : Num B) {n : ℕ} →
   ∀ (xs ys : Vec A n) →
   let numV₁ = toNumV num₁ {n}
       (_+₁_ , _-₁_ , _*₁_) = (Num._+_ numV₁ , Num._-_ numV₁ , Num._*_ numV₁)
       numV₂ = toNumV num₂ {n}
       (_+₂_ , _-₂_ , _*₂_) = (Num._+_ numV₂ , Num._-_ numV₂ , Num._*_ numV₂)
   in map trans (xs +₁ ys) ≡ (map trans xs +₂ map trans ys) ×
      map trans (xs -₁ ys) ≡ (map trans xs -₂ map trans ys) ×
      map trans (xs *₁ ys) ≡ (map trans xs *₂ map trans ys)

expand-correct : ∀ {A n}
  → {{num : Num A}}
  → {toNumV : (∀ {A : Set} → Num A → ∀ {n} → Num (Vec A n))}
  → numV-natural toNumV
  → (e : Expr (Vec A n)) → (xs : Vec A n)
  → semantics1 {{toNumV num}} e xs ≡
       map (λ e → semantics n e (toNest n xs))
            (expand n {{toNumV (toExprNumN n)}} e)
expand-correct _ Ind xs = refl-Ind xs
expand-correct {n = n} _ (Lit ys) xs
   rewrite map-compose (λ e → semantics n e (toNest n xs)) (liftVal n) ys
         | map-cong (λ x → semantics n (liftVal n x) (toNest n xs))
               (λ x → x) (sem-lift-cancel n (toNest n xs)) ys
         | map-id ys
   = refl
expand-correct {n = n} {{num}} {toNumV} toNumVNat (Add e₀ e₁) xs
   rewrite expand-correct toNumVNat e₀ xs
         | expand-correct toNumVNat e₁ xs
         | proj₁ (toNumVNat (λ e → semantics n e (toNest n xs))
                    (toExprNumN n) num
                    (expand n {{toNumV (toExprNumN n)}} e₀)
                    (expand n {{toNumV (toExprNumN n)}} e₁))
   = refl
expand-correct {n = n} {{num}} {toNumV} toNumVNat (Sub e₀ e₁) xs
   rewrite expand-correct toNumVNat e₀ xs
         | expand-correct toNumVNat e₁ xs
         | proj₁ (proj₂
             (toNumVNat (λ e → semantics n e (toNest n xs))
                    (toExprNumN n) num
                    (expand n {{toNumV (toExprNumN n)}} e₀)
                    (expand n {{toNumV (toExprNumN n)}} e₁)))
   = refl
expand-correct {n = n} {{num}} {toNumV} toNumVNat (Mul e₀ e₁) xs
   rewrite expand-correct toNumVNat e₀ xs
         | expand-correct toNumVNat e₁ xs
         | proj₂ (proj₂
             (toNumVNat (λ e → semantics n e (toNest n xs))
                    (toExprNumN n) num
                    (expand n {{toNumV (toExprNumN n)}} e₀)
                    (expand n {{toNumV (toExprNumN n)}} e₁)))
   = refl

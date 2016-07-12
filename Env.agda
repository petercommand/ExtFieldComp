module _ where
open import Data.Nat
open import Data.Nat.Base
open import Data.Nat.Show
open import Data.Integer using (ℤ)
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.String
open import Data.Maybe
open import Data.Bool
open import Data.Vec using (Vec)
open import Function
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality

module ListEquality where
  L== : ∀ {A : Set} -> (A -> A -> Bool) -> List A -> List A -> Bool
  L== op [] [] = true
  L== op [] (x ∷ list2) = false
  L== op (x ∷ list1) [] = false
  L== op (x ∷ list1) (x₁ ∷ list2) with op x x₁
  ... | true = L== op list1 list2
  ... | false = false

Env : Set
Env = List (String × List ℕ) -- List of (symbol × List address)


lookup : String -> Env -> Maybe $ List ℕ
lookup n [] = nothing
lookup n ((proj₁ , proj₂) ∷ list) with n == proj₁
... | true = just proj₂
... | false = lookup n list

lookupLen : String -> (n : ℕ) -> Env -> Maybe $ Vec ℕ n
lookupLen str n [] = nothing
lookupLen str n ((proj₁ , proj₂) ∷ env) with Data.String._≟_ str proj₁ | Data.Nat._≟_ n (Data.List.length proj₂)
lookupLen str .(foldr (λ _ → suc) 0 proj₂) ((.str , proj₂) ∷ env) | yes refl | yes refl = just (Data.Vec.fromList proj₂)
lookupLen str n ((.str , proj₂) ∷ env) | yes refl | no p = lookupLen str n env
... | no p | m = lookupLen str n env

putEnvVal : ℕ × List ℕ -> Env -> Env
putEnvVal (proj₁ , proj₂) env = (Data.Nat.Show.show proj₁ , proj₂) ∷ env

putEnvConst : String × List ℕ -> Env -> Env
putEnvConst x env = x ∷ env

removeEnvConst : String × List ℕ -> Env -> Env
removeEnvConst _ [] = []
removeEnvConst (proj₁ , proj₂) ((proj₃ , proj₄) ∷ env) with ListEquality.L== (λ x y -> case x Data.Nat.≟ y of
                                                                                     λ { (yes m) -> true
                                                                                       ; (no _) -> false }) proj₂ proj₄ | proj₁ Data.String.≟ proj₃

... | true | yes _ = env
... | _    | _ = removeEnvConst (proj₁ , proj₂) env


removeEnvVal : ℕ × List ℕ -> Env -> Env
removeEnvVal (proj₁ , proj₂) env = removeEnvConst (Data.Nat.Show.show proj₁ , proj₂) env


CompState : Set
CompState = ℕ × Env



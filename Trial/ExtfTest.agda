open import Data.Nat
open import Data.Integer hiding (suc)
open import Data.Fin
open import Data.Product hiding (zip)
open import Data.Vec hiding (zipWith; zip)


open import Relation.Binary.PropositionalEquality
import Relation.Binary.HeterogeneousEquality as H
zipWith : ∀ {l m n}{A : Set l}{B : Set m}{C : Set n}
    -> (f : A -> B -> C) -> A × A -> B × B -> C × C
zipWith f (proj₁ , proj₂) (proj₃ , proj₄) = f proj₁ proj₃ , f proj₂ proj₄

Nest : ℕ → Set → Set
Nest zero A = A
Nest (suc n) A = Nest n A × Nest n A

data Expr (A : Set) : ℕ -> Set where
  Let : ∀ {n} -> Expr A n -> Expr A (suc n) -> Expr A n
  LetC : ∀ {n} -> A -> Expr A (suc n) -> Expr A n
  Var : ∀ {n} -> Fin n -> Expr A n
  Add : ∀ {n} -> Expr A n -> Expr A n -> Expr A n
--  Mul : ∀ {n} -> Expr A n -> Expr A n -> Expr A n

Addr = ℕ

data TAC : Set where
  ConstI : Addr -> ℤ -> TAC
  AddI : Addr -> Addr -> Addr -> TAC
--  SubI : Addr -> Addr -> Addr -> TAC
--  Mul : Addr -> Addr -> Addr -> TAC

Env : (K : Set) -> ℕ -> Set
Env K n = Vec K n

expandLet : ∀ {m n} → Nest n (Expr ℕ m) → Nest n (Expr ℕ (suc m)) → Nest n (Expr ℕ m)
expandLet {n = zero} x x₁ = Let x x₁
expandLet {n = suc n} x x₁ = zipWith (expandLet {_} {n}) x x₁

expandLetC : ∀ {m n} → Nest n ℕ → Nest n (Expr ℕ (suc m)) → Nest n (Expr ℕ m)
expandLetC {n = zero} x x₁ = LetC x x₁
expandLetC {n = suc n} x x₁ = zipWith (expandLetC {_} {n}) x x₁

expandAdd : ∀ {m n} → Nest n (Expr ℕ m) → Nest n (Expr ℕ m) → Nest n (Expr ℕ m)
expandAdd {n = zero} x x₁ = Add x x₁
expandAdd {n = suc n} x x₁ = zipWith (expandAdd {_} {n}) x x₁

expand : ∀ {m n} → Expr (Nest n ℕ) m → Nest n (Expr ℕ m)
expand {n = n} (Let exp exp₁)
   = let e = expand {_} {n} exp
         e₁ = expand {_} {n} exp₁
     in expandLet {_} {n} e e₁
expand {n = n} (LetC x exp)
   = let e = expand {_} {n} exp
     in expandLetC {_} {n} x e
expand {n = zero} (Var x) = Var x
expand {n = suc n} (Var x) = expand {_} {n} (Var x) , expand {_} {n} (Var x)
expand {n = n} (Add exp exp₁)
   = let e1 = expand {_} {n} exp
         e2 = expand {_} {n} exp₁
     in expandAdd {_} {n} e1 e2

eval : ∀ {n} -> Env ℕ n -> Expr ℕ n -> ℕ
eval env (Let exp exp₁) = eval (eval env exp ∷ env) exp₁
eval env (LetC x exp) = eval (x ∷ env) exp
eval env (Var x) = lookup x env
eval env (Add exp exp₁) = eval env exp Data.Nat.+ eval env exp₁

_^_ : ℕ -> ℕ -> ℕ
_^_ = ^' 1
  where
    ^' : ℕ -> ℕ -> ℕ -> ℕ
    ^' acc x zero = acc
    ^' acc x (suc y) = ^' (acc Data.Nat.* x) x y

postulate
  ^-lem : ∀ n -> (2 ^ n) Data.Nat.+ (2 ^ n) ≡ (2 ^ (suc n))

group' : ∀ {l}{K : Set l}{n} -> (vec : Vec K (2 ^ suc n))
    -> ∃₂ λ (v1 v2 : Vec K (2 ^ n)) -> v1 ++ v2 H.≅ vec
group' vec = {!!} , ({!!} , {!!})

flatten : {K : Set} -> (n : ℕ) -> Nest n K -> Vec K (2 ^ n)
flatten zero nest = nest ∷ []
flatten (suc n) (proj₁ , proj₂) rewrite sym (^-lem n) = flatten n proj₁ ++ flatten n proj₂

reconstruct : {K : Set} -> (n : ℕ) -> Vec K (2 ^ n) -> Nest n K
reconstruct zero (x ∷ []) = x
reconstruct (suc n) vec = {!!}

vecExchange : ∀ {A : Set}{a b}
   -> Vec (Vec A a) b
   -> Vec (Vec A b) a
vecExchange [] = replicate []
vecExchange (vec ∷ vec₁) = let ev = vecExchange vec₁
                            in Data.Vec.zipWith (_∷_) vec ev


eval' : ∀ {m n} -> Env (Vec ℕ (2 ^ n)) m -> Expr (Nest n ℕ) m -> Nest n ℕ
eval' {_} {n} env (Let expr expr₁) = eval' {_} {n} (flatten n (eval' {_} {n} env expr) ∷ env) expr₁
eval' {_} {n}  env (LetC x expr) = eval' {_} {n} (flatten n x ∷ env) expr
eval' {_} {n} env (Var x) = reconstruct n (lookup x env)
eval' {_} {n} env (Add expr expr₁)
   = reconstruct n (Data.Vec.zipWith (Data.Nat._+_)
         (flatten n (eval' {_} {n} env expr)) (flatten n (eval' {_} {n} env expr₁)))

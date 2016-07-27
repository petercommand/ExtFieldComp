module _ where

open import Data.Product
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.Vec hiding (_++_)

open import Relation.Binary.PropositionalEquality

data Expr : ℕ → Set where
  num : ∀ {n} → (k : ℕ) → Expr n
  var : ∀ {n} → (i : Fin n) → Expr n
  _∔_ : ∀ {n} → (e₀ : Expr n) → (e₁ : Expr n) → Expr n
  lett : ∀ {n} → (e₀ : Expr n) → (e₁ : Expr (suc n)) → Expr n

Env : ℕ → Set
Env = Vec ℕ

eval : ∀ {n} → Env n → Expr n → ℕ
eval env (num k) = k
eval env (var i) = lookup i env
eval env (e₀ ∔ e₁) = eval env e₀ + eval env e₁
eval env (lett e₀ e₁) = eval (eval env e₀ ∷ env) e₁

Addr : Set
Addr = ℕ

data TAC : Set where
  store : ℕ → Addr → TAC
  add   : Addr → Addr → Addr → TAC

SymTab : ℕ → Set
SymTab = Vec Addr

  -- compile returns a triple:
  --   (code, location of result, next space counter)

compile : ∀ {n} → Addr → SymTab n → Expr n → (List TAC × Addr × Addr)
compile c stab (num k) = store k c ∷ [] , c , suc c
compile c stab (var i) = [] , lookup i stab , c
compile c₀ stab (e₀ ∔ e₁) with compile c₀ stab e₀
... | p₀ , a₀ , c₁        with compile c₁ stab e₁
... | p₁ , a₁ , c₂ = p₀ ++ p₁ ++ add a₀ a₁ c₂ ∷ [] , c₂ , suc c₂
compile c₀ stab (lett e₀ e₁) with compile c₀ stab e₀
... | p₀ , a₀ , c₁           with compile c₁ (a₀ ∷ stab) e₁
... | p₁ , a₁ , c₂ = p₀ ++ p₁ , a₁ , c₂

Heap : Set
Heap = List (Addr × ℕ)

postulate
  putHeap : Addr → ℕ → Heap → Heap
  getHeap : Addr → Heap → ℕ

  get-put : ∀ c k h → getHeap c (putHeap c k h) ≡ k

run : List TAC → Heap → Heap
run [] h = h
run (store v a ∷ p) h = run p (putHeap a v h)
run (add a₀ a₁ a₂ ∷ p) h =
  run p (putHeap a₂ (getHeap a₀ h + getHeap a₁ h) h)

run-compose : ∀ p₀ p₁ h →
    run (p₀ ++ p₁) h ≡ run p₁ (run p₀ h)
run-compose [] p₁ _ = refl
run-compose (store v a ∷ p₀) p₁ h
  rewrite run-compose p₀ p₁ (putHeap a v h) = refl
run-compose (add a₀ a₁ a₂ ∷ p₀) p₁ h
  rewrite run-compose p₀ p₁ (putHeap a₂ (getHeap a₀ h + getHeap a₁ h) h) = refl

data Consist (h : Heap) : ∀ {n} → Env n → SymTab n → Set where
  [] : Consist h [] []
  _∷_ : ∀ {a v n} {env : Env n} {stab : SymTab n}
      → getHeap a h ≡ v → Consist h env stab
      → Consist h (v ∷ env) (a ∷ stab)

postulate
  consist : ∀ {h n} {env : Env n} {stab : SymTab n}
          → Consist h env stab
          → ∀ i → getHeap (lookup i stab) h ≡ lookup i env

comp-correct : ∀ {n}
   → (e : Expr n) (env : Env n) (c : Addr) (stab : SymTab n) (h : Heap)
   → Consist h env stab
   → let res = compile c stab e
         p = proj₁ res
         a = proj₁ (proj₂ res)
     in getHeap a (run p h) ≡ eval env e
comp-correct (num k) env c stab h cons = get-put c k h
comp-correct (var i) env c stab h cons = consist cons i
comp-correct (e₀ ∔ e₁) env c₀ stab h cons
    with comp-correct e₀ env c₀ stab h cons
... | a₀↦e₀↓
    with compile c₀ stab e₀
... | p₀ , a₀ , c₁
    with comp-correct e₁ env c₁ stab (run p₀ h) {!   !}
... | a₁↦e₁↓
    with compile c₁ stab e₁
... | p₁ , a₁ , c₂
  rewrite run-compose p₀ (p₁ ++ add a₀ a₁ c₂ ∷ []) h
        | run-compose p₁ (add a₀ a₁ c₂ ∷ []) (run p₀ h)
        | get-put c₂ (getHeap a₀ (run p₁ (run p₀ h)) +
                      getHeap a₁ (run p₁ (run p₀ h))) (run p₁ (run p₀ h))
        | a₁↦e₁↓ = {!   !}
comp-correct (lett e₀ e₁) env c₀ stab h cons with
     comp-correct e₀ env c₀ stab h cons
... | a₀↦e₀↓        with compile c₀ stab e₀
... | p₀ , a₀ , c₁  with
     comp-correct e₁ (eval env e₀ ∷ env) c₁ (a₀ ∷ stab) (run p₀ h)
         (a₀↦e₀↓ ∷ {!   !})
... | a₁↦e₁↓        with compile c₁ (a₀ ∷ stab) e₁
... | p₁ , a₁ , c₂ rewrite run-compose p₀ p₁ h
   = a₁↦e₁↓

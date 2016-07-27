module _ where

open import Data.Product
open import Data.Nat
open import Data.Fin hiding (_+_; _≤_; _<_)
open import Data.List
open import Data.Vec hiding (_++_)
open import Data.Empty

open import NatProperties

open import Relation.Nullary
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
  get-put' : ∀ {k} c c' h → ¬ c ≡ c' → getHeap c (putHeap c' k h) ≡ getHeap c h

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

heap-inc : ∀ {n}
   → (e : Expr n) (c : Addr) (stab : SymTab n)
   → let c₀ = proj₂ (proj₂ (compile c stab e))
     in c₀ ≥ c
heap-inc (num k) c stab = ≤weak (s≤s ≤-refl) 
heap-inc (var i) c stab = ≤-refl
heap-inc (e ∔ e₁) c₀ stab
    with heap-inc e c₀ stab
... | c₁≥c₀
    with compile c₀ stab e
... | p₀ , a₀ , c₁
    with heap-inc e₁ c₁ stab
... | c₂≥c₁
    with compile c₁ stab e₁
... | p₁ , a₁ , c₂ rewrite +suc-1 c₂
    = ≤-trans c₁≥c₀ (≤-weakening c₁ c₂ 1 c₂≥c₁)
heap-inc (lett e e₁) c₀ stab
    with heap-inc e c₀ stab
... | c₁≥c₀
    with compile c₀ stab e
... | p₀ , a₀ , c₁
    with heap-inc e₁ c₁ (a₀ ∷ stab)
... | c₂≥c₁
    with compile c₁ (a₀ ∷ stab) e₁
... | p₁ , a₁ , c₂
    = ≤-trans c₁≥c₀ c₂≥c₁

comp-preserve-heap-content : ∀ {n}
   → (e : Expr n) (c : Addr) (stab : SymTab n) (h : Heap)
   → (a : ℕ)
   → a < c
   → let (p , _ , _) = compile c stab e
     in getHeap a h ≡ getHeap a (run p h)
comp-preserve-heap-content (num k) (suc c) stab h a (s≤s a<c) =
    sym (get-put' a (suc c) h (a<c->¬a≡c a (suc c) (s≤s a<c)))
comp-preserve-heap-content (var i) (suc c) stab h m (s≤s a<c) = refl
comp-preserve-heap-content (e ∔ e₁) (suc c) stab h m (s≤s a<c)
    with comp-preserve-heap-content e (suc c) stab h m (s≤s a<c)
... | pre1
    with heap-inc e (suc c) stab
... | inc1
    with compile (suc c) stab e
... | p₀ , a₀ , c₁
    with heap-inc e₁ c₁ stab
... | inc2
    with comp-preserve-heap-content e₁ c₁ stab h m (≤-trans (suc-<-intro a<c) inc1)
... | pre2
    with compile c₁ stab e₁
... | p₁ , a₁ , c₂ rewrite run-compose p₀ (p₁ ++ add a₀ a₁ c₂ ∷ []) h
                         | run-compose p₁ (add a₀ a₁ c₂ ∷ []) (run p₀ h)
                         = {!!}
comp-preserve-heap-content (lett e e₁) (suc c) stab h m (s≤s a<c) = {!!}

run-preserve-consist : ∀ {n}
   → (e : Expr n) (env : Env n) (c : Addr) (stab : SymTab n) (h : Heap)
   → Consist h env stab
   → let res = compile c stab e
         p = proj₁ res
         a = proj₁ (proj₂ res)
     in Consist (run p h) env stab
run-preserve-consist (num k) env c stab h cons = {!!}
run-preserve-consist (var i) env c stab h cons = {!!}
run-preserve-consist (e ∔ e₁) env c stab h cons = {!!}
run-preserve-consist (lett e e₁) env c stab h cons = {!!}

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

module _ where

open import Data.Product
open import Data.Nat
open import Data.Fin hiding (_+_; _≤_; _<_)
open import Data.List
open import Data.Vec hiding (_++_)
open import Data.Empty

open import NatProperties
open import ListProperties

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

_:>_ : ∀ {l} (K : Set l) (a : K) -> K
a :> b = b


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

target : TAC -> Addr
target (store x addr) = addr
target (add addr1 addr2 addr3) = addr3

data CodeAddrIrrelevance : List TAC → Addr → Set where
  ⟦⟧ : ∀ {addr} -> CodeAddrIrrelevance [] addr
  _∶∶∶_ : ∀ {addr} {code : TAC} {code' : List TAC}
                               → (notequal : ¬ (target code ≡ addr))
                               → CodeAddrIrrelevance code' addr
                               → CodeAddrIrrelevance (code' ++ (code ∷ [])) addr

aux : ∀ {K : Set} (list : List K) → list ++ [] ≡ list
aux [] = refl
aux (x ∷ list) = cong (_∷_ x) (aux list)

listAux : ∀ {K : Set} (list : List K) (elem : K)
     → ¬ (list ++ elem ∷ [] ≡ [])
listAux [] elem ()
listAux (x ∷ list) elem ()

listAux' : ∀ {K : Set} (elem : K) -> ¬ elem ∷ [] ≡ List K :> []
listAux' elem ()

aux' : ∀ {addr code} → CodeAddrIrrelevance (code ++ []) addr
                   → CodeAddrIrrelevance code addr
aux' {addr} {code} irre rewrite aux code = irre

aux'-re : ∀ {addr code} → CodeAddrIrrelevance code addr
                        → CodeAddrIrrelevance (code ++ []) addr
aux'-re {addr} {code} irre rewrite aux code = irre

-- code ∷ code' ≡ code ∷ [] ++  code' ≡ code' ++ code ∷ []
irreComm' : ∀ code code' addr → CodeAddrIrrelevance (code ++ code') addr
                              → CodeAddrIrrelevance (code' ++ code) addr
irreComm' code [] addr irre = {!!}
irreComm' code (x ∷ code') addr irre = {!!}

aux''' : ∀ code code' addr → ¬ target code ≡ addr
                           → CodeAddrIrrelevance code' addr
                           → CodeAddrIrrelevance (code' ++ (code ∷ [])) addr
aux'''  code code' addr noteq irre = noteq ∶∶∶ irre

aux'' : ∀ code code' addr → ¬ target code ≡ addr
                          → CodeAddrIrrelevance code' addr
                          → CodeAddrIrrelevance (code ∷ code') addr
aux'' code [] addr ¬≡ irre = ¬≡ ∶∶∶ ⟦⟧
aux'' (store x x₁) (x₂ ∷ code') addr ¬≡ irre = {!!}
aux'' (add x x₁ x₂) (x₃ ∷ code') addr ¬≡ irre = {!!}

combAux : ∀ addr code code' code''
        → (¬ (target code ≡ addr))
        → CodeAddrIrrelevance (code' ++ code'') addr
        → CodeAddrIrrelevance ((code' ++ code ∷ []) ++ code'') addr
combAux addr code code' [] notequal irre rewrite aux (code' ++ code ∷ [])
    = notequal ∶∶∶ aux' {addr} {code'} irre
combAux addr code [] code'' notequal irre = {!!}
combAux addr code (x ∷ code') code'' notequal irre = {!!}

codeAddrIrrelevanceComb : ∀ {addr code code'}
   → CodeAddrIrrelevance code addr
   → CodeAddrIrrelevance code' addr
   → CodeAddrIrrelevance (code ++ code') addr
codeAddrIrrelevanceComb ⟦⟧ irre2 = irre2
codeAddrIrrelevanceComb {addr} {code' = []}
   (_∶∶∶_ {code = store x x₁} {[]} notequal irre1) irre2
     = notequal ∶∶∶ irre2
codeAddrIrrelevanceComb {addr} {code' = x₂ ∷ code'}
   (_∶∶∶_ {code = store x x₁} {[]} notequal irre1) irre2
     = combAux addr (store x x₁) [] (x₂ ∷ code') notequal irre2
codeAddrIrrelevanceComb {addr} {code' = code''}
   (_∶∶∶_ {code = store x x₁} {x₂ ∷ code'} notequal irre1) irre2
     = combAux addr (store x x₁) (x₂ ∷ code') code'' notequal
          (codeAddrIrrelevanceComb irre1 irre2)
codeAddrIrrelevanceComb {addr} {code' = []}
   (_∶∶∶_ {code = add x x₁ x₂} {[]} notequal irre1) irre2
     = notequal ∶∶∶ irre2
codeAddrIrrelevanceComb {addr} {code' = x₃ ∷ code'}
   (_∶∶∶_ {code = add x x₁ x₂} {[]} notequal irre1) irre2
     = combAux addr (add x x₁ x₂) [] (x₃ ∷ code') notequal irre2
codeAddrIrrelevanceComb {addr} {code' = []}
   (_∶∶∶_ {code = add x x₁ x₂} {x₃ ∷ code'} notequal irre1) irre2
     = combAux addr (add x x₁ x₂) (x₃ ∷ code') [] notequal (aux'-re irre1)
codeAddrIrrelevanceComb {addr} {code' = x₄ ∷ code''}
   (_∶∶∶_ {code = add x x₁ x₂} {x₃ ∷ code'} notequal irre1) irre2
     = combAux addr (add x x₁ x₂) (x₃ ∷ code') (x₄ ∷ code'') notequal
          (codeAddrIrrelevanceComb irre1 irre2)
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

comp-a<c : ∀ {n}
   → (e : Expr n) (c : Addr) (stab : SymTab n)
   → let p , a , c = compile c stab e
     in a < c
comp-a<c (num k) c stab = s≤s ≤-refl
comp-a<c (var i) c stab = {!!}
comp-a<c (e ∔ e₁) c stab = s≤s ≤-refl
comp-a<c (lett e e₁) c stab
    with compile c stab e
... | p₀ , a₀ , c₀
    with comp-a<c e₁ c₀ (a₀ ∷ stab)
... | a<c
    with compile c₀ (a₀ ∷ stab) e₁
... | p₁ , a₁ , c₁ = a<c


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

comp-irrelevance : ∀ {n} c₀ c₁ → c₀ < c₁
   → (e : Expr n) (stab : SymTab n)
   → CodeAddrIrrelevance (proj₁ (compile c₁ stab e)) c₀
comp-irrelevance zero zero () e stab
comp-irrelevance (suc c₀) zero () e stab
comp-irrelevance zero _ (s≤s 0≤c₀) (num k) stab = (λ ()) ∶∶∶ ⟦⟧
comp-irrelevance zero _ (s≤s 0≤c₀) (var i) stab = ⟦⟧
comp-irrelevance zero (suc c₀) (s≤s 0≤c₀) (e ∔ e₁) stab
    with heap-inc e (suc c₀) stab
... | inc1
    with comp-irrelevance zero (suc c₀) (s≤s z≤n) e stab
... | irre1
    with compile (suc c₀) stab e
... | p₀ , a₀ , c₁
    with heap-inc e₁ c₁ stab
... | inc2
    with comp-irrelevance zero c₁ (≤-trans (suc-<-intro 0≤c₀) inc1) e₁ stab
... | irre2
    with codeAddrIrrelevanceComb irre1 irre2
... | irre3
    with compile c₁ stab e₁
... | p₁ , a₁ , c₂ rewrite ++-assoc p₀ p₁ (add a₀ a₁ c₂ ∷ [])
    =  (a<c->¬c≡a 0 c₂ (≤-trans (suc-<-intro 0≤c₀) (≤-trans inc1 inc2))) ∶∶∶ irre3
comp-irrelevance zero (suc c₀) (s≤s 0<c₀) (lett e e₁) stab
    with heap-inc e (suc c₀) stab
... | inc1
    with comp-irrelevance zero (suc c₀) (s≤s 0<c₀) e stab
... | irre1
    with compile (suc c₀) stab e
... | p₀ , a₀ , c₁
    with heap-inc e₁ c₁ (a₀ ∷ stab)
... | inc2
    with comp-irrelevance zero c₁ (≤-trans (suc-<-intro 0<c₀) inc1) e₁ (a₀ ∷ stab)
... | irre2
    with codeAddrIrrelevanceComb irre1 irre2
... | irre3
    with compile c₁ (a₀ ∷ stab) e₁
... | p₁ , a₁ , c₂ = irre3
comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) (num k) stab
    = a<c->¬c≡a (suc c₀) (suc c₁) (s≤s c₀<c₁) ∶∶∶ ⟦⟧
comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) (var i) stab = ⟦⟧
comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) (e ∔ e₁) stab
    with heap-inc e (suc c₁) stab
... | inc1
    with comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) e stab
... | irre1
    with compile (suc c₁) stab e
... | p₀ , a₀ , c₂
    with heap-inc e₁ c₂ stab
... | inc2
    with comp-irrelevance (suc c₀) c₂ (≤-trans (suc-<-intro c₀<c₁) inc1) e₁ stab
... | irre2
    with codeAddrIrrelevanceComb irre1 irre2
... | irre3
    with compile c₂ stab e₁
... | p₁ , a₁ , c₃ rewrite ++-assoc p₀ p₁ (add a₀ a₁ c₃ ∷ [])
    = (a<c->¬c≡a (suc c₀) c₃ (≤-trans (suc-<-intro c₀<c₁)
                              (≤-trans inc1 inc2))) ∶∶∶ irre3
comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) (lett e e₁) stab
    with heap-inc e (suc c₁) stab
... | inc1
    with comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) e stab
... | irre1
    with compile (suc c₁) stab e
... | p₀ , a₀ , c₂
    with heap-inc e₁ c₂ (a₀ ∷ stab)
... | inc2
    with comp-irrelevance (suc c₀) c₂ (≤-trans (suc-<-intro c₀<c₁) inc1) e₁ (a₀ ∷ stab)
... | irre2
    with codeAddrIrrelevanceComb irre1 irre2
... | irre3
    with compile c₂ (a₀ ∷ stab) e₁
... | p₁ , a₁ , c₃ rewrite ++-assoc p₀ p₁ (add a₀ a₁ c₃ ∷ [])
    = irre3

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


codeAddrIrrelevance->ignorable : ∀ code code' addr h
                            -> CodeAddrIrrelevance code addr
                            -> getHeap addr (run code (run code' h)) ≡
                               getHeap addr (run code' h)
codeAddrIrrelevance->ignorable .[] code' addr h ⟦⟧ = refl
codeAddrIrrelevance->ignorable .(store x x₁ ∷ []) code'' addr h
      (_∶∶∶_ {code = store x x₁} {[]} notequal irre)
        rewrite get-put' {x} addr x₁ (run code'' h) (λ x₂ → notequal (sym x₂))
           = refl
codeAddrIrrelevance->ignorable .(x₂ ∷ code' ++ store x x₁ ∷ []) code'' addr h
      (_∶∶∶_ {code = store x x₁} {x₂ ∷ code'} notequal irre)
        rewrite run-compose (x₂ ∷ code') (store x x₁ ∷ []) (run code'' h)
              | get-put' {x} addr x₁ (run (x₂ ∷ code') (run code'' h))
                                     (λ x₃ → notequal (sym x₃))
                 = codeAddrIrrelevance->ignorable (x₂ ∷ code') code'' addr h irre
codeAddrIrrelevance->ignorable .(add x x₁ x₂ ∷ []) code'' addr h
      (_∶∶∶_ {code = add x x₁ x₂} {[]} notequal irre)
         rewrite get-put' {getHeap x (run code'' h) + getHeap x₁ (run code'' h)}
                            addr x₂ (run code'' h) (λ x₃ → notequal (sym x₃))
         = refl
codeAddrIrrelevance->ignorable .(x₃ ∷ code' ++ add x x₁ x₂ ∷ []) code'' addr h
      (_∶∶∶_ {code = add x x₁ x₂} {x₃ ∷ code'} notequal irre)
          rewrite run-compose (x₃ ∷ code') (add x x₁ x₂ ∷ []) (run code'' h)
                | get-put' {getHeap x (run (x₃ ∷ code') (run code'' h)) +
                             getHeap x₁ (run (x₃ ∷ code') (run code'' h))}
                          addr x₂ (run (x₃ ∷ code') (run code'' h))
                              (λ x₄ → notequal (sym x₄))
                  = codeAddrIrrelevance->ignorable (x₃ ∷ code') code'' addr h irre

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
    with run-preserve-consist e₀ env c₀ stab h cons
... | pre-e₀
    with heap-inc e₀ c₀ stab
... | inc1
    with
         let p₀ , a₀ , c₁ = compile c₀ stab e₀
             p₁ , a₁ , c₂ = compile c₁ stab e₁
         in comp-irrelevance a₀ c₁ (comp-a<c e₀ c₀ stab) e₁ stab
... | irre1
    with compile c₀ stab e₀
... | p₀ , a₀ , c₁
    with comp-correct e₁ env c₁ stab (run p₀ h) pre-e₀ 
... | a₁↦e₁↓
    with compile c₁ stab e₁
... | p₁ , a₁ , c₂
  rewrite run-compose p₀ (p₁ ++ add a₀ a₁ c₂ ∷ []) h
        | run-compose p₁ (add a₀ a₁ c₂ ∷ []) (run p₀ h)
        | get-put c₂ (getHeap a₀ (run p₁ (run p₀ h)) +
                      getHeap a₁ (run p₁ (run p₀ h))) (run p₁ (run p₀ h))
        | a₁↦e₁↓
        | codeAddrIrrelevance->ignorable p₁ p₀ a₀ h irre1
        | a₀↦e₀↓ = refl
comp-correct (lett e₀ e₁) env c₀ stab h cons
    with comp-correct e₀ env c₀ stab h cons
... | a₀↦e₀↓
    with run-preserve-consist e₀ env c₀ stab h cons
... | pre1
    with compile c₀ stab e₀
... | p₀ , a₀ , c₁
    with comp-correct e₁ (eval env e₀ ∷ env) c₁ (a₀ ∷ stab) (run p₀ h)
         (a₀↦e₀↓ ∷ pre1)
... | a₁↦e₁↓
    with compile c₁ (a₀ ∷ stab) e₁
... | p₁ , a₁ , c₂
    rewrite run-compose p₀ p₁ h
   = a₁↦e₁↓

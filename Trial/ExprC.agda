module _ where

open import Data.Product
open import Data.Nat hiding (_+_; _*_)
open import Data.Fin hiding (_+_; _-_; _≤_; _<_)
open import Data.List
open import Data.Vec hiding (_++_)
open import Data.Empty
open import Data.Integer hiding (suc; _≤_)

open import NatProperties
open import ListProperties

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Complex

_:>_ : ∀ {l} (K : Set l) (a : K) -> K
a :> b = b


data Expr : ℕ → Set where
  num : ∀ {n} → (k : ℂ) → Expr n
  var : ∀ {n} → (i : Fin n) → Expr n
  _∔_ : ∀ {n} → (e₀ : Expr n) → (e₁ : Expr n) → Expr n
  _∙_ : ∀ {n} → (e₀ : Expr n) → (e₁ : Expr n) → Expr n
  lett : ∀ {n} → (e₀ : Expr n) → (e₁ : Expr (suc n)) → Expr n

Env : ℕ → Set
Env = Vec ℂ

eval : ∀ {n} → Env n → Expr n → ℂ
eval env (num k) = k
eval env (var i) = lookup i env
eval env (e₀ ∔ e₁) = eval env e₀ ℂ+ eval env e₁
eval env (e₀ ∙ e₁) = eval env e₀ ℂ* eval env e₁
eval env (lett e₀ e₁) = eval (eval env e₀ ∷ env) e₁

Addr : Set
Addr = ℕ

data TAC : Set where
  store : ℤ → Addr → TAC
  add   : Addr → Addr → Addr → TAC
  sub   : Addr → Addr → Addr → TAC
  mul   : Addr → Addr → Addr → TAC

target : TAC -> Addr
target (store x addr) = addr
target (add addr1 addr2 addr3) = addr3  -- addr3 = addr1 - addr2
target (sub addr1 addr2 addr3) = addr3  -- addr3 = addr1 - addr2
target (mul addr1 addr2 addr3) = addr3  -- addr3 = addr1 * addr2

data CodeAddrIrrelevance : List TAC → Addr → Set where
  ⟦⟧ : ∀ {addr} -> CodeAddrIrrelevance [] addr
  _∶∶∶_ : ∀ {addr} {code : TAC} {code' : List TAC}
                               → (notequal : ¬ (target code ≡ addr))
                               → CodeAddrIrrelevance code' addr
                               → CodeAddrIrrelevance (code' ++ (code ∷ [])) addr

postulate
  irreInterchange : ∀ {addr code code'} → CodeAddrIrrelevance (code ++ code') addr
                                        → CodeAddrIrrelevance (code' ++ code) addr
  irreSplit : ∀ {addr} code code' → CodeAddrIrrelevance (code ++ code') addr
                                  → CodeAddrIrrelevance code addr ×
                                    CodeAddrIrrelevance code' addr
  irreComb : ∀ {addr code code'}
       → CodeAddrIrrelevance code addr
       → CodeAddrIrrelevance code' addr
       → CodeAddrIrrelevance (code ++ code') addr

SymTab : ℕ → Set
SymTab = Vec (Addr × Addr)

  -- compile returns a triple:
  --   (code, location of result, next space counter)

compile : ∀ {n} → Addr → SymTab n → Expr n → (List TAC × (Addr × Addr) × Addr)
compile c stab (num (ℂb r i))
    = store r c ∷ store i (suc c) ∷ [] , (c , suc c) , suc (suc c)
compile c stab (var i) = [] , lookup i stab , c
compile c₀ stab (e₀ ∔ e₁)    with compile c₀ stab e₀
... | p₀ , (ar₀ , ai₀) , c₁  with compile c₁ stab e₁
... | p₁ , (ar₁ , ai₁) , c₂
    = p₀ ++ p₁ ++ add ar₀ ar₁ c₂ ∷ add ai₀ ai₁ (suc c₂) ∷ [] ,
         (c₂ , suc c₂) , suc (suc c₂)
compile c₀ stab (e₀ ∙ e₁)    with compile c₀ stab e₀
... | p₀ , (ar₀ , ai₀) , c₁  with compile c₁ stab e₁
... | p₁ , (ar₁ , ai₁) , c₂
    = p₀ ++ p₁ ++ add ar₀ ar₁ c₂ ∷                  
                   add ai₀ ai₁ (suc c₂) ∷           
                   mul ar₀ ai₁ (suc-n c₂ 2) ∷       
                   mul ar₁ ai₀ (suc-n c₂ 3) ∷     
                   add (suc-n c₂ 2) (suc-n c₂ 3) (suc-n c₂ 4) ∷
                   sub c₂ (suc-n c₂ 4) (suc-n c₂ 5) ∷ [] ,
                                ((suc-n c₂ 5) , -- real comp addr
                                 (suc-n c₂ 4))  -- img comp addr
                                 , suc-n c₂ 6 -- c₂ + 6
compile c₀ stab (lett e₀ e₁) with compile c₀ stab e₀
... | p₀ , a₀ , c₁           with compile c₁ (a₀ ∷ stab) e₁
... | p₁ , a₁ , c₂ = p₀ ++ p₁ , a₁ , c₂

postulate
  Heap : Set

postulate
  putHeap : Addr → ℤ → Heap → Heap
  getHeap : Addr → Heap → ℤ
  get-put : ∀ c k h → getHeap c (putHeap c k h) ≡ k
  get-put' : ∀ {k} c c' h → ¬ c ≡ c' → getHeap c (putHeap c' k h) ≡ getHeap c h

run : List TAC → Heap → Heap
run [] h = h
run (store v a ∷ p) h = run p (putHeap a v h)
run (add a₀ a₁ a₂ ∷ p) h =
  run p (putHeap a₂ (getHeap a₀ h + getHeap a₁ h) h)
run (sub a₀ a₁ a₂ ∷ p) h =
  run p (putHeap a₂ (getHeap a₀ h - getHeap a₁ h) h)
run (mul a₀ a₁ a₂ ∷ p) h =
  run p (putHeap a₂ (getHeap a₀ h * getHeap a₁ h) h)


run-compose : ∀ p₀ p₁ h →
    run (p₀ ++ p₁) h ≡ run p₁ (run p₀ h)
run-compose [] p₁ _ = refl
run-compose (store v a ∷ p₀) p₁ h
  rewrite run-compose p₀ p₁ (putHeap a v h) = refl
run-compose (add a₀ a₁ a₂ ∷ p₀) p₁ h
  rewrite run-compose p₀ p₁ (putHeap a₂ (getHeap a₀ h + getHeap a₁ h) h) = refl
run-compose (sub a₀ a₁ a₂ ∷ p₀) p₁ h
  rewrite run-compose p₀ p₁ (putHeap a₂ (getHeap a₀ h - getHeap a₁ h) h) = refl
run-compose (mul a₀ a₁ a₂ ∷ p₀) p₁ h
  rewrite run-compose p₀ p₁ (putHeap a₂ (getHeap a₀ h * getHeap a₁ h) h) = refl

data Consist : ∀ {n} → Heap → Env n → SymTab n → ℕ → Set where
  [] : ∀ {h} → Consist h [] [] 0
  _∷_ : ∀ {h a1 a2 v1 v2 n o p} {env : Env n} {stab : SymTab n}
      → getHeap a1 h ≡ v1 × getHeap a2 h ≡ v2 × a1 < o × a2 < o × o ≤ p
      → Consist h env stab o
      → Consist h (ℂb v1 v2 ∷ env) ((a1 , a2) ∷ stab) p
  inc : ∀ {h n o} {env : Env n} {stab : SymTab n}
        → Consist h env stab o
        → ∀ p → o ≤ p → Consist h env stab p


consist : ∀ h n env stab c (i : Fin n) → Consist {n} h env stab c
          → let a₀ , a₁ = lookup i stab
            in (ℂb (getHeap a₀ h) (getHeap a₁ h)) ≡ lookup i env
consist h .0 .[] .[] .0 () []
consist h _ _ _ c zero ((proj₁ , proj₂ , proj₃) ∷ cons) rewrite proj₂ | proj₁ = refl
consist h _ _ _ c (suc i) ((proj₁ , proj₂ , proj₃) ∷ cons) = consist h _ _ _ _ i cons
consist h n env stab c i (inc cons .c x₁) = consist h n env stab _ i cons

heap-inc : ∀ {n}
   → (e : Expr n) (c : Addr) (stab : SymTab n)
   → let c₀ = proj₂ (proj₂ (compile c stab e))
     in c₀ ≥ c
heap-inc (num (ℂb r i)) c stab = ≤weak (s≤s (a≤suc-a c))
heap-inc (var i) c stab = ≤-refl
heap-inc (e ∔ e₁) c₀ stab
    with heap-inc e c₀ stab
... | c₁≥c₀
    with compile c₀ stab e
... | p₀ , a₀ , c₁
    with heap-inc e₁ c₁ stab
... | c₂≥c₁
    with compile c₁ stab e₁
... | p₁ , a₁ , c₂
    = ≤-trans c₁≥c₀ (≤-trans c₂≥c₁ (≤weak (≤weak (s≤s (s≤s ≤-refl)))))
heap-inc (e ∙ e₁) c₀ stab
    with heap-inc e c₀ stab
... | c₁≥c₀
    with compile c₀ stab e
... | p₀ , a₀ , c₁
    with heap-inc e₁ c₁ stab
... | c₂≥c₁
    with compile c₁ stab e₁
... | p₁ , a₁ , c₂
    = ≤-trans c₁≥c₀ (≤-trans c₂≥c₁ (a≤-suc-n-a c₂ 6))
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
comp-irrelevance zero _ (s≤s 0≤c₀) (num (ℂb r i)) stab
    = a<c->¬c≡a zero (suc (suc _)) (s≤s z≤n) ∶∶∶ (¬suc-a≡zero _ ∶∶∶ ⟦⟧)
comp-irrelevance zero _ (s≤s 0≤c₀) (var i) stab = ⟦⟧
comp-irrelevance zero (suc c₀) (s≤s 0≤c₀) (e ∔ e₁) stab
    with heap-inc e (suc c₀) stab
... | inc1
    with comp-irrelevance zero (suc c₀) (s≤s z≤n) e stab
... | irre1
    with compile (suc c₀) stab e
... | p₀ , (ar₀ , ai₀) , c₁
    with heap-inc e₁ c₁ stab
... | inc2
    with comp-irrelevance zero c₁ (≤-trans (suc-<-intro 0≤c₀) inc1) e₁ stab
... | irre2
    with irreComb irre1 irre2
... | irre3
    with compile c₁ stab e₁
... | p₁ , (ar₁ , ai₁) , c₂
    rewrite ++-assoc p₀ p₁ (add ar₀ ar₁ c₂ ∷ add ai₀ ai₁ (suc c₂) ∷ [])
    =  irreComb irre3 (irreComb {_} {add ar₀ ar₁ c₂ ∷ []}
          (a<c->¬c≡a 0 c₂ (≤-trans (s≤s 0≤c₀) (≤-trans inc1 inc2)) ∶∶∶ ⟦⟧)
           ((λ ()) ∶∶∶ ⟦⟧))
comp-irrelevance zero (suc c₀) (s≤s 0≤c₀) (e ∙ e₁) stab
    with heap-inc e (suc c₀) stab
... | inc1
    with comp-irrelevance zero (suc c₀) (s≤s z≤n) e stab
... | irre1
    with compile (suc c₀) stab e
... | p₀ , (ar₀ , ai₀) , c₁
    with heap-inc e₁ c₁ stab
... | inc2
    with comp-irrelevance zero c₁ (≤-trans (suc-<-intro 0≤c₀) inc1) e₁ stab
... | irre2
    with irreComb irre1 irre2
... | irre3
    with compile c₁ stab e₁
... | p₁ , (ar₁ , ai₁) , c₂
    rewrite ++-assoc p₀ p₁ (add ar₀ ar₁ c₂ ∷
                            add ai₀ ai₁ (suc c₂) ∷
                            mul ar₀ ai₁ (suc (suc c₂)) ∷
                            mul ar₁ ai₀ (suc (suc (suc c₂))) ∷
       add (suc (suc c₂)) (suc (suc (suc c₂))) (suc (suc (suc (suc c₂)))) ∷
       sub c₂ (suc (suc (suc (suc c₂)))) (suc (suc (suc (suc (suc c₂))))) ∷ [])
    = irreComb irre3 {!!}
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
    with irreComb irre1 irre2
... | irre3
    with compile c₁ (a₀ ∷ stab) e₁
... | p₁ , a₁ , c₂ = irre3
comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) (num (ℂb r i)) stab
    = irreComb {_} {store r (suc c₁) ∷ []}
         (a<c->¬c≡a _ _ (s≤s c₀<c₁) ∶∶∶ ⟦⟧)
         (a<c->¬c≡a _ _ (s≤s (s≤s (≤weak c₀<c₁))) ∶∶∶ ⟦⟧)
comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) (var i) stab = ⟦⟧
comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) (e ∔ e₁) stab
    with heap-inc e (suc c₁) stab
... | inc1
    with comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) e stab
... | irre1
    with compile (suc c₁) stab e
... | p₀ , (ar₀ , ai₀) , c₂
    with heap-inc e₁ c₂ stab
... | inc2
    with comp-irrelevance (suc c₀) c₂ (≤-trans (suc-<-intro c₀<c₁) inc1) e₁ stab
... | irre2
    with irreComb irre1 irre2
... | irre3
    with compile c₂ stab e₁
... | p₁ , (ar₁ , ai₁) , c₃
    rewrite ++-assoc p₀ p₁ (add ar₀ ar₁ c₃ ∷ add ai₀ ai₁ (suc c₃) ∷ [])
    = irreComb irre3 (irreComb
         (a<c->¬c≡a _ _ (≤-trans (≤-trans (s≤s c₀<c₁) inc1) inc2) ∶∶∶ ⟦⟧)
         (a<c->¬c≡a _ _ (s≤s (≤-trans c₀<c₁ (≤-trans (≤weak inc1) inc2))) ∶∶∶ ⟦⟧))
comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) (e ∙ e₁) stab = {!!}
comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) (lett e e₁) stab
    with heap-inc e (suc c₁) stab
... | inc1
    with comp-irrelevance (suc c₀) (suc c₁) (s≤s c₀<c₁) e stab
... | irre1
    with compile (suc c₁) stab e
... | p₀ , (ar₀ , ai₀) , c₂
    with heap-inc e₁ c₂ ((ar₀ , ai₀) ∷ stab)
... | inc2
    with comp-irrelevance (suc c₀) c₂ (≤-trans (suc-<-intro c₀<c₁) inc1)
                        e₁ ((ar₀ , ai₀) ∷ stab)
... | irre2
    with irreComb irre1 irre2
... | irre3
    with compile c₂ ((ar₀ , ai₀) ∷ stab) e₁
... | p₁ , (ar₁ , ai₁) , c₃ rewrite ++-assoc p₀ p₁ (add ar₀ ar₁ c₃ ∷ add ai₀ ai₁ (suc c₃) ∷ [])
    = irre3
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
codeAddrIrrelevance->ignorable .(sub x x₁ x₂ ∷ []) code'' addr h
      (_∶∶∶_ {code = sub x x₁ x₂} {[]} notequal irre)
         rewrite get-put' {getHeap x (run code'' h) - getHeap x₁ (run code'' h)}
                            addr x₂ (run code'' h) (λ x₃ → notequal (sym x₃))
         = refl
codeAddrIrrelevance->ignorable .(x₃ ∷ code' ++ sub x x₁ x₂ ∷ []) code'' addr h
      (_∶∶∶_ {code = sub x x₁ x₂} {x₃ ∷ code'} notequal irre)
          rewrite run-compose (x₃ ∷ code') (sub x x₁ x₂ ∷ []) (run code'' h)
                | get-put' {getHeap x (run (x₃ ∷ code') (run code'' h)) -
                             getHeap x₁ (run (x₃ ∷ code') (run code'' h))}
                          addr x₂ (run (x₃ ∷ code') (run code'' h))
                              (λ x₄ → notequal (sym x₄))
                  = codeAddrIrrelevance->ignorable (x₃ ∷ code') code'' addr h irre
codeAddrIrrelevance->ignorable .(mul x x₁ x₂ ∷ []) code'' addr h
      (_∶∶∶_ {code = mul x x₁ x₂} {[]} notequal irre)
         rewrite get-put' {getHeap x (run code'' h) * getHeap x₁ (run code'' h)}
                            addr x₂ (run code'' h) (λ x₃ → notequal (sym x₃))
         = refl
codeAddrIrrelevance->ignorable .(x₃ ∷ code' ++ mul x x₁ x₂ ∷ []) code'' addr h
      (_∶∶∶_ {code = mul x x₁ x₂} {x₃ ∷ code'} notequal irre)
          rewrite run-compose (x₃ ∷ code') (mul x x₁ x₂ ∷ []) (run code'' h)
                | get-put' {getHeap x (run (x₃ ∷ code') (run code'' h)) *
                             getHeap x₁ (run (x₃ ∷ code') (run code'' h))}
                          addr x₂ (run (x₃ ∷ code') (run code'' h))
                              (λ x₄ → notequal (sym x₄))
                  = codeAddrIrrelevance->ignorable (x₃ ∷ code') code'' addr h irre


rpc-aux : ∀ {c d k n o}
   → (env : Env n) (stab : SymTab n) (h : Heap)
   → c ≥ o
   → d ≥ c
   → Consist h env stab o
   → Consist (putHeap c k h) env stab d
rpc-aux .[] .[] h _ _ [] = inc [] _ z≤n
rpc-aux _ _ h c≥o d≥c ((proj₁ , proj₂ , proj₃ , proj₄ , proj₅) ∷ cons)
    = (trans (get-put' _ _ h (a<c->¬a≡c _ _
              (≤-trans (≤-trans proj₃ proj₅) c≥o))) proj₁ ,
                    ((trans (get-put' _ _ h (a<c->¬a≡c _ _
          (≤-trans (≤-trans proj₄ proj₅) c≥o))) proj₂) ,
              ((≤-trans (≤-trans proj₃ proj₅) c≥o) ,
                 ((≤-trans (≤-trans proj₄ proj₅) c≥o) , d≥c)))) ∷
                    rpc-aux _ _ _ (≤-trans proj₅ c≥o) ≤-refl cons
rpc-aux env stab h c≥o d≥c (inc cons o x)
    = rpc-aux env stab h (≤-trans x c≥o) d≥c cons


found-><c : ∀ {n}
   → (env : Env n) (c : Addr) (stab : SymTab n) (h : Heap)
   → Consist h env stab c
   → ∀ (i : Fin n) → let a₀ , a₁ = lookup i stab
                     in a₀ < c × a₁ < c
found-><c .[] .0 .[] h [] ()
found-><c _ c _ h ((proj₁ , proj₂ , proj₃ , proj₄ , proj₅) ∷ cons) zero
   = ≤-trans proj₃ proj₅ , ≤-trans proj₄ proj₅
found-><c _ c _ h ((proj₁ , proj₂ , proj₃ , proj₄ , proj₅) ∷ cons) (suc i)
   = found-><c _ c _ h (inc cons c proj₅) i
found-><c env c stab h (inc {o = o} cons .c x) zero
   = let r1 , r2 = found-><c _ o _ h cons zero
     in ≤-trans r1 x , ≤-trans r2 x
found-><c env c stab h (inc {o = o} cons .c x) (suc i)
   = let r1 , r2 = found-><c _ o _ h cons (suc i)
     in ≤-trans r1 x , ≤-trans r2 x

consist-reduce : ∀ {e₀ a₀ n}
   → (env : Env n) (c : Addr) (stab : SymTab n) (h : Heap)
   → Consist h (e₀ ∷ env) (a₀ ∷ stab) c
   → Consist h env stab c
consist-reduce env c [] h ((proj₁ , _ , proj₃) ∷ cons)
    = inc cons c (proj₂ (proj₂ proj₃))
consist-reduce env c (x ∷ stab) h ((proj₁ , _ , proj₃) ∷ cons)
    = inc cons c (proj₂ (proj₂ proj₃))
consist-reduce env c stab h (inc cons .c x)
    = inc (consist-reduce env _ stab h cons) c x


comp-correct : ∀ {n}
   → (e : Expr n) (env : Env n) (c : Addr) (stab : SymTab n) (h : Heap)
   → Consist h env stab c
   → let p , (ar , ai) , c₀ = compile c stab e
     in ℂb (getHeap ar (run p h)) (getHeap ai (run p h)) ≡ eval env e × ar < c₀ × ai < c₀ × Consist (run p h) env stab c₀
comp-correct (num (ℂb r i)) env c stab h cons
    rewrite get-put' {i} c (suc c) (putHeap c r h) (λ ())
          | get-put (suc c) i (putHeap c r h)
          | get-put c r h = refl , (a≤suc-a (suc c)) ,
            (≤-refl , rpc-aux env stab (putHeap c r h) (a≤suc-a c) (a≤suc-a (suc c))
               (rpc-aux env stab h ≤-refl ≤-refl cons))
comp-correct (var i) env c stab h cons
    = consist h _ env stab c i cons , proj₁ (found-><c env c stab h cons i) ,
         proj₂ (found-><c env c stab h cons i) , cons
comp-correct (e₀ ∔ e₁) env c₀ stab h cons
    with comp-correct e₀ env c₀ stab h cons
... | correct0 , ar₀<c₁ , ai₀<c₁ , cons_e₀
    with heap-inc e₀ c₀ stab
... | inc1
    with let p₀ , (ar₀ , ai₀) , c₁ = compile c₀ stab e₀
         in comp-irrelevance ar₀ c₁ ar₀<c₁ e₁ stab ,
              comp-irrelevance ai₀ c₁ ai₀<c₁ e₁ stab
... | irrer1 , irrei1
    with compile c₀ stab e₀
... | p₀ , (ar₀ , ai₀) , c₁
    with comp-correct e₁ env c₁ stab (run p₀ h) cons_e₀
... | correct1 , ar₁<c₂ , ai₁<c₂ , cons_e₁
    with heap-inc e₁ c₁ stab
... | inc2
    with compile c₁ stab e₁
... | p₁ , (ar₁ , ai₁) , c₂
    rewrite run-compose p₀ (p₁ ++ add ar₀ ar₁ c₂ ∷ add ai₀ ai₁ (suc c₂) ∷ []) h
          | run-compose p₁ (add ar₀ ar₁ c₂ ∷ add ai₀ ai₁ (suc c₂) ∷ []) (run p₀ h)
          | get-put' {getHeap ai₀ (putHeap c₂
            (getHeap ar₀ (run p₁ (run p₀ h)) +
              getHeap ar₁ (run p₁ (run p₀ h)))
               (run p₁ (run p₀ h)))
            +
            getHeap ai₁ (putHeap c₂
               (getHeap ar₀ (run p₁ (run p₀ h)) + getHeap ar₁ (run p₁ (run p₀ h)))
                  (run p₁ (run p₀ h)))}
                  c₂ (suc c₂) ((putHeap c₂
                       (getHeap ar₀ (run p₁ (run p₀ h)) +
                        getHeap ar₁ (run p₁ (run p₀ h)))
                          (run p₁ (run p₀ h)))) (λ ())
          | get-put c₂ (getHeap ar₀ (run p₁ (run p₀ h)) + getHeap ar₁
             (run p₁ (run p₀ h))) (run p₁ (run p₀ h))
          | get-put (suc c₂) (getHeap ai₀
         (putHeap c₂
          (getHeap ar₀ (run p₁ (run p₀ h)) + getHeap ar₁ (run p₁ (run p₀ h)))
          (run p₁ (run p₀ h)))
         +
         getHeap ai₁
         (putHeap c₂
          (getHeap ar₀ (run p₁ (run p₀ h)) + getHeap ar₁ (run p₁ (run p₀ h)))
          (run p₁ (run p₀ h)))) (putHeap c₂
         (getHeap ar₀ (run p₁ (run p₀ h)) + getHeap ar₁ (run p₁ (run p₀ h)))
         (run p₁ (run p₀ h)))
          | get-put' {getHeap ar₀ (run p₁ (run p₀ h)) + getHeap ar₁
                      (run p₁ (run p₀ h))}
                      ai₀ c₂ (run p₁ (run p₀ h)) (a<c->¬a≡c _ _ (≤-trans ai₀<c₁ inc2))
          | get-put' {getHeap ar₀ (run p₁ (run p₀ h)) + getHeap ar₁
                      (run p₁ (run p₀ h))}
                      ai₁ c₂ (run p₁ (run p₀ h)) (a<c->¬a≡c _ _ ai₁<c₂)
          | sym correct0
          | sym correct1
          | codeAddrIrrelevance->ignorable p₁ p₀ ar₀ h irrer1
          | codeAddrIrrelevance->ignorable p₁ p₀ ai₀ h irrei1
          = refl , a≤suc-a (suc c₂) , ≤-refl , rpc-aux env stab
          (putHeap c₂
            (getHeap ar₀ (run p₀ h) + getHeap ar₁ (run p₁ (run p₀ h)))
              (run p₁ (run p₀ h)))
              (a≤suc-a c₂)
              (a≤suc-a (suc c₂))
              (rpc-aux _ _ (run p₁ (run p₀ h)) ≤-refl ≤-refl cons_e₁)
comp-correct (e₀ ∙ e₁) env c₀ stab h cons
    with comp-correct e₀ env c₀ stab h cons
... | correct0 , ar₀<c₁ , ai₀<c₁ , cons_e₀
    with heap-inc e₀ c₀ stab
... | inc1
    with let p₀ , (ar₀ , ai₀) , c₁ = compile c₀ stab e₀
         in comp-irrelevance ar₀ c₁ ar₀<c₁ e₁ stab ,
              comp-irrelevance ai₀ c₁ ai₀<c₁ e₁ stab
... | irrer1 , irrei1
    with compile c₀ stab e₀
... | p₀ , (ar₀ , ai₀) , c₁
    with comp-correct e₁ env c₁ stab (run p₀ h) cons_e₀
... | correct1 , ar₁<c₂ , ai₁<c₂ , cons_e₁
    with heap-inc e₁ c₁ stab
... | inc2
    with compile c₁ stab e₁
... | p₁ , (ar₁ , ai₁) , c₂
    rewrite run-compose p₀ (p₁ ++
         add ar₀ ar₁ c₂ ∷
         add ai₀ ai₁ (suc c₂) ∷
         mul ar₀ ai₁ (suc (suc c₂)) ∷
         mul ar₁ ai₀ (suc (suc (suc c₂))) ∷
         add (suc (suc c₂)) (suc (suc (suc c₂))) (suc (suc (suc (suc c₂))))
         ∷
         sub c₂ (suc (suc (suc (suc c₂)))) (suc (suc (suc (suc (suc c₂)))))
         ∷ []) h
           | run-compose p₁ (add ar₀ ar₁ c₂ ∷
         add ai₀ ai₁ (suc c₂) ∷
         mul ar₀ ai₁ (suc (suc c₂)) ∷
         mul ar₁ ai₀ (suc (suc (suc c₂))) ∷
         add (suc (suc c₂)) (suc (suc (suc c₂))) (suc (suc (suc (suc c₂))))
         ∷
         sub c₂ (suc (suc (suc (suc c₂)))) (suc (suc (suc (suc (suc c₂)))))
         ∷ []) (run p₀ h)
    = {!!} , {!!} , {!!} , {!!}
comp-correct {_} (lett e₀ e₁) env c₀ stab h cons
    with comp-correct e₀ env c₀ stab h cons
... | correct0 , ar₀<c₁ , ai₀<c₁ , cons_e₀
    with heap-inc e₀ c₀ stab
... | inc1
    with compile c₀ stab e₀
... | p₀ , (ar₀ , ai₀) , c₁
    with
      let ℂb r i = eval env e₀ 
      in comp-correct {_} e₁ (eval env e₀ ∷ env) c₁ ((ar₀ , ai₀) ∷ stab) (run p₀ h)
            (_∷_ {v1 = r} {v2 = i}
              (cong ℂ.r correct0 , cong ℂ.i correct0 ,
                 ar₀<c₁ , ai₀<c₁ , ≤-refl) cons_e₀)
... | correct1 , ar₁<c₂ , ai₁<c₂ , cons_e₁
    with heap-inc e₁ c₁ ((ar₀ , ai₀) ∷ stab)
... | inc2
    with compile c₁ ((ar₀ , ai₀) ∷ stab) e₁
... | p₁ , (ar₁ , ai₁) , c₂
    rewrite run-compose p₀ p₁ h
    = correct1 , ar₁<c₂ , ai₁<c₂ , consist-reduce env c₂ stab _ cons_e₁

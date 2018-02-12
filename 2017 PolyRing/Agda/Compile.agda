module Compile where

open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (_⊔_)
open import Data.List
open import Data.Product
open import Data.Vec hiding (_>>=_) renaming (_++_ to _v++_)
open import Num
open import NatProperties
open import Data.Nat.Properties.Simple
open import Level hiding (zero; suc)
open import Function
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality

open import PolyRing

Addr : Set
Addr = ℕ

data TAC (A : Set) : Set where
  ConstI : Addr → A → TAC A
  AddI   : Addr → Addr → Addr → TAC A
  SubI   : Addr → Addr → Addr → TAC A
  MulI   : Addr → Addr → Addr → TAC A

Ins : Set → Set
Ins A = List (TAC A)

-- A simple state monad

record SSA (A : Set) : Set where
  constructor ssa
  field
    ssa1 : Addr → A × Addr

return : ∀ {A : Set} → A → SSA A
return a = ssa (λ x → a , x)

_>>=_ : ∀ {A B : Set} → SSA A → (A → SSA B) → SSA B
ssa x >>= f = ssa (λ args → let r , s = x args
                                ssa s' = f r
                            in s' s)
infixr 10 _>>=_

alloc : SSA Addr
alloc = ssa (λ n → (n , suc n))

biOpSSA : ∀ {A : Set}
          → (Addr → Addr → Addr → TAC A)
          → SSA (Addr × Ins A) → SSA (Addr × Ins A)
          → SSA (Addr × Ins A)
biOpSSA op p1 p2 =
    p1 >>= λ x →
    p2 >>= λ y →
    alloc >>= λ dest →
    let (addr1 , ins1) = x
        (addr2 , ins2) = y
    in return (dest , ins1 ++ ins2 ++ (op dest addr1 addr2 ∷ []))

instance SSANum : ∀ {A : Set} → Num (SSA (Addr × Ins A))

SSANum = record { _+_ = biOpSSA AddI
                ; _-_ = biOpSSA SubI
                ; _*_ = biOpSSA MulI }

pass : ∀ {A B : Set} → A → SSA (A × Ins B)
pass r = return (r , [])

compile0 : ∀ {A : Set} → A → SSA (Addr × Ins A)
compile0 v = alloc >>= λ addr →
             return (addr , ConstI addr v ∷ [])

compile : ∀ {A : Set} (n : ℕ) → Vec Addr n
        → ExprN A n → SSA (Addr × Ins A)
compile zero addr exp = compile0 exp
compile {A} (suc n) (x ∷ addr) exp = foldExpr (pass x) (compile n addr) exp

-- running a program

postulate
  Heap : Set → Set
postulate
  putHeap : ∀ {A : Set} → Addr → A → Heap A → Heap A
  getHeap : ∀ {A : Set} → Addr → Heap A → A
  get-put : ∀ {A : Set} → ∀ c (k : A) h → getHeap c (putHeap c k h) ≡ k
  get-put' : ∀ {A : Set} → ∀ c c' (k : A) h → ¬ c ≡ c'
                         → getHeap c (putHeap c' k h) ≡ getHeap c h


target : ∀ {A : Set} {{_ : Num A}} → TAC A → Addr
target (ConstI x₁ x₂) = x₁
target (AddI x₁ x₂ x₃) = x₁
target (SubI x₁ x₂ x₃) = x₁
target (MulI x₁ x₂ x₃) = x₁

runIns : ∀ {A : Set} {{_ : Num A}} → Heap A → Ins A → Heap A
runIns h [] = h
runIns h (ConstI x₁ x₂ ∷ ins) = runIns (putHeap x₁ x₂ h) ins
runIns {{num}} h (AddI x₁ x₂ x₃ ∷ ins)
  = let a₂ = getHeap x₂ h
        a₃ = getHeap x₃ h
        _+_ = Num._+_ num
    in runIns (putHeap x₁ (a₂ + a₃) h) ins
runIns {{num}} h (SubI x₁ x₂ x₃ ∷ ins)
  = let a₂ = getHeap x₂ h
        a₃ = getHeap x₃ h
        _-_ = Num._-_ num
    in runIns (putHeap x₁ (a₂ - a₃) h) ins
runIns {{num}} h (MulI x₁ x₂ x₃ ∷ ins)
  = let a₂ = getHeap x₂ h
        a₃ = getHeap x₃ h
        _*_ = Num._*_ num
    in runIns (putHeap x₁ (a₂ * a₃) h) ins

runSSA : ∀ {A : Set} {{_ : Num A}}
       → SSA (Addr × Ins A) → Addr → Heap A → A
runSSA (ssa m) r₀ h =
  let ((r , ins) , _) = m r₀
  in getHeap r (runIns h ins)

runCompile : ∀ {A : Set} {{_ : Num A}} {n : ℕ}
           → Vec Addr n → Addr → ExprN A n → Heap A → A
runCompile {n = n} rs r₀ e h =
   runSSA (compile n rs e) r₀ h

data HeapCons {A : Set} (h : Heap A) :
        ∀ {n : ℕ} → DChain A n → Vec Addr n → Set where
  [] : HeapCons h tt []
  _∷_ : ∀ {n : ℕ} {es rs e r}
         → ((num : Num A) → getHeap r h ≡ semantics {{num}} n e es)
         → HeapCons h {n} es rs
         → HeapCons h (e , es) (r ∷ rs)
data All {a b} {A : Set a}
         (P : A → Set b) : (n : ℕ) → Vec A n → Set (a ⊔ b) where
  [] : All P 0 []
  _∷_ : ∀ {n x xs} (px : P x) (pxs : All P n xs) → All P (suc n) (x ∷ xs)

allInc : ∀ {n a b}{vec : Vec ℕ n}
   -> a ≤ b
   -> All (\x -> x < a) n vec
   -> All (\x -> x < b) n vec
allInc p [] = []
allInc p (px ∷ vecAll) = ≤-trans px p ∷ allInc p vecAll

All-P : ∀ {l m n o} {A : Set l}{vec : Vec A o} {P : A → Set m} {Q : A → Set n}
   → All P o vec
   → (∀ {a : A} → P a → Q a)
   → All Q o vec
All-P [] p = []
All-P (px ∷ all₁) p = p px ∷ All-P all₁ p



data LAll {a b} {A : Set a}
          (P : A → Set b) : List A → Set (a ⊔ b) where
  [] : LAll P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : LAll P xs) → LAll P (x ∷ xs)


LAll-P : ∀ {l m n} {A : Set l}{list : List A} {P : A → Set m} {Q : A → Set n}
   → LAll P list
   → (∀ {a : A} → P a → Q a)
   → LAll Q list
LAll-P [] p = []
LAll-P (px ∷ all₁) p = p px ∷ LAll-P all₁ p


LAll++ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys : List A} →
        LAll P xs → LAll P ys → LAll P (xs ++ ys)
LAll++ []         pys = pys
LAll++ (px ∷ pxs) pys = px ∷ LAll++ pxs pys


Ignorable : (A : Set) {{_ : Num A}} → ℕ → Ins A → Set
Ignorable _ n = LAll (λ x → ¬ n ≡ target x)

all-decomp : ∀ {K : Set}{P : K -> Set}(list : List K) (all : LAll P list) -> length list > 0
    -> ∃ (λ x -> ∃ (λ y -> LAll P x × LAll P (y ∷ []) × (x ++ (y ∷ []) ≡ list) × (length x < length list)))
all-decomp [] [] ()
all-decomp (x ∷ []) (px ∷ []) (s≤s p) = [] , x , [] , px ∷ [] , refl , s≤s z≤n
all-decomp (x ∷ xs ∷ xss) (px ∷ px₁ ∷ all) p = let head , elem , headp , elemp , pr , pr2 = all-decomp (xs ∷ xss) (px₁ ∷ all) (s≤s z≤n)
                                               in x ∷ head , elem , px ∷ headp , elemp , cong (\y -> x ∷ y) pr , s≤s pr2

runIns-compose : ∀ {A : Set} {{_ : Num A}} (ins1 ins2 : Ins A) (h : Heap A)
   → runIns h (ins1 ++ ins2) ≡ runIns (runIns h ins1) ins2
runIns-compose [] ins2 h = refl
runIns-compose (ConstI x₁ x₂ ∷ ins1) ins2 h = runIns-compose ins1 ins2 _
runIns-compose (AddI x₁ x₂ x₃ ∷ ins1) ins2 h = runIns-compose ins1 ins2 _
runIns-compose (SubI x₁ x₂ x₃ ∷ ins1) ins2 h = runIns-compose ins1 ins2 _
runIns-compose (MulI x₁ x₂ x₃ ∷ ins1) ins2 h = runIns-compose ins1 ins2 _



ignore : ∀ {A : Set} {{_ : Num A}} → ∀ r₀ ins₀
  → Ignorable A r₀ ins₀
  → Acc (length ins₀)
  → ∀ h
  → getHeap r₀ (runIns {A} h ins₀) ≡ getHeap r₀ h
ignore r₀ [] ign _ h = refl
ignore r₀ (x₁ ∷ ins₀) ign ac h with all-decomp (x₁ ∷ ins₀) ign (s≤s z≤n)
ignore {A} r₀ (x₁ ∷ ins₀) ign (acc ac) h | head₁ , ConstI x₂ x₃ , head_p , tail_p ∷ [] , p , len_p
   rewrite sym p
         | runIns-compose head₁ (ConstI x₂ x₃ ∷ []) h
         | get-put' {A} r₀ x₂ x₃ (runIns h head₁) tail_p
         = ignore r₀ head₁ head_p (ac (length head₁) len_p) h
ignore {A} {{num}} r₀ (x₁ ∷ ins₀) ign (acc ac) h | head₁ , AddI x₂ x₃ x₄ , head_p , tail_p ∷ [] , p , len_p
   rewrite sym p
         | runIns-compose head₁ (AddI x₂ x₃ x₄ ∷ []) h
         | get-put' {A} r₀ x₂ ((num Num.+ getHeap x₃ (runIns h head₁)) (getHeap x₄ (runIns h head₁))) (runIns h head₁) tail_p
         = ignore r₀ head₁ head_p (ac (length head₁) len_p) h
ignore {A} {{num}} r₀ (x₁ ∷ ins₀) ign (acc ac) h | head₁ , SubI x₂ x₃ x₄ , head_p , tail_p ∷ [] , p , len_p
   rewrite sym p
         | runIns-compose head₁ (SubI x₂ x₃ x₄ ∷ []) h
         | get-put' {A} r₀ x₂ ((num Num.- getHeap x₃ (runIns h head₁)) (getHeap x₄ (runIns h head₁))) (runIns h head₁) tail_p
         = ignore r₀ head₁ head_p (ac (length head₁) len_p) h
ignore {A} {{num}} r₀ (x₁ ∷ ins₀) ign (acc ac) h | head₁ , MulI x₂ x₃ x₄ , head_p , tail_p ∷ [] , p , len_p
   rewrite sym p
         | runIns-compose head₁ (MulI x₂ x₃ x₄ ∷ []) h
         | get-put' {A} r₀ x₂ ((num Num.* getHeap x₃ (runIns h head₁)) (getHeap x₄ (runIns h head₁))) (runIns h head₁) tail_p
         = ignore r₀ head₁ head_p (ac (length head₁) len_p) h

HeapInc : ∀ (A : Set) {{_ : Num A}} (n : ℕ)
  → Set
HeapInc A n = ∀ n₀ env expr → let (ret , ins) , n₁ = SSA.ssa1 (compile {A} n env expr) n₀
                                in n₁ ≥ n₀

compHeapInc : ∀ {A : Set} {{_ : Num A}} (n : ℕ) → HeapInc A n
compHeapInc zero n₀ env expr = (≤-suc n₀ n₀ ≤-refl)
compHeapInc (suc n) n₀ (x₁ ∷ env) (Ind) = ≤-refl
compHeapInc (suc n) n₀ (x₁ ∷ env) (Lit x₂) = compHeapInc n _ _ _
compHeapInc (suc n) n₀ (x₁ ∷ env) (Add expr expr₁)
    with compHeapInc (suc n) n₀ (x₁ ∷ env) expr
... | inc₀
    with compile (suc n) (x₁ ∷ env) expr
... | comp₀
    with SSA.ssa1 comp₀ n₀
... | (ret₀ , ins₀) , n₁
    with compHeapInc (suc n) n₁ (x₁ ∷ env) expr₁
... | inc₁
    with compile (suc n) (x₁ ∷ env) expr₁
... | comp₁
    with SSA.ssa1 comp₁ n₁
... | (ret₁ , ins₁) , n₂ = ≤-trans inc₀ (≤-trans inc₁ (≤-suc n₂ n₂ ≤-refl))
compHeapInc (suc n) n₀ (x₁ ∷ env) (Sub expr expr₁)
    with compHeapInc (suc n) n₀ (x₁ ∷ env) expr
... | inc₀
    with compile (suc n) (x₁ ∷ env) expr
... | comp₀
    with SSA.ssa1 comp₀ n₀
... | (ret₀ , ins₀) , n₁
    with compHeapInc (suc n) n₁ (x₁ ∷ env) expr₁
... | inc₁
    with compile (suc n) (x₁ ∷ env) expr₁
... | comp₁
    with SSA.ssa1 comp₁ n₁
... | (ret₁ , ins₁) , n₂ = ≤-trans inc₀ (≤-trans inc₁ (≤-suc n₂ n₂ ≤-refl))
compHeapInc (suc n) n₀ (x₁ ∷ env) (Mul expr expr₁)
    with compHeapInc (suc n) n₀ (x₁ ∷ env) expr
... | inc₀
    with compile (suc n) (x₁ ∷ env) expr
... | comp₀
    with SSA.ssa1 comp₀ n₀
... | (ret₀ , ins₀) , n₁
    with compHeapInc (suc n) n₁ (x₁ ∷ env) expr₁
... | inc₁
    with compile (suc n) (x₁ ∷ env) expr₁
... | comp₁
    with SSA.ssa1 comp₁ n₁
... | (ret₁ , ins₁) , n₂ = ≤-trans inc₀ (≤-trans inc₁ (≤-suc n₂ n₂ ≤-refl))

InsAddrInc : ∀ (A : Set) {{_ : Num A}} (n : ℕ) → Set
InsAddrInc A n = ∀ n₀ env expr → let (ret , ins) , n₁ =
                                            SSA.ssa1 (compile {A} n env expr) n₀
                                 in LAll (λ x → target x ≥ n₀) ins

compInsAddrInc : ∀ {A : Set} {{_ : Num A}} (n : ℕ) → InsAddrInc A n
compInsAddrInc zero n₀ [] expr = ≤-refl ∷ []
compInsAddrInc (suc n) n₀ (x₁ ∷ env) Ind = []
compInsAddrInc (suc n) n₀ (x₁ ∷ env) (Lit x₂) = compInsAddrInc n n₀ env x₂
compInsAddrInc (suc n) n₀ (x₁ ∷ env) (Add expr expr₁)
  = LAll++ (compInsAddrInc (suc n) n₀ (x₁ ∷ env) expr)
      (LAll++ (LAll-P (compInsAddrInc (suc n) _ (x₁ ∷ env) expr₁)
         (λ x → ≤-trans (compHeapInc (suc n) n₀ (x₁ ∷ env) expr) x))
           ((≤-trans (compHeapInc (suc n) n₀ (x₁ ∷ env) expr)
               (≤-trans (compHeapInc (suc n) _ (x₁ ∷ env) expr₁)
                  ≤-refl)) ∷ []))
compInsAddrInc (suc n) n₀ (x₁ ∷ env) (Sub expr expr₁)
  = LAll++ (compInsAddrInc (suc n) n₀ (x₁ ∷ env) expr)
      (LAll++ (LAll-P (compInsAddrInc (suc n) _ (x₁ ∷ env) expr₁)
         (λ x → ≤-trans (compHeapInc (suc n) n₀ (x₁ ∷ env) expr) x))
           ((≤-trans (compHeapInc (suc n) n₀ (x₁ ∷ env) expr)
               (≤-trans (compHeapInc (suc n) _ (x₁ ∷ env) expr₁)
                  ≤-refl)) ∷ []))
compInsAddrInc (suc n) n₀ (x₁ ∷ env) (Mul expr expr₁)
  = LAll++ (compInsAddrInc (suc n) n₀ (x₁ ∷ env) expr)
      (LAll++ (LAll-P (compInsAddrInc (suc n) _ (x₁ ∷ env) expr₁)
         (λ x → ≤-trans (compHeapInc (suc n) n₀ (x₁ ∷ env) expr) x))
           ((≤-trans (compHeapInc (suc n) n₀ (x₁ ∷ env) expr)
               (≤-trans (compHeapInc (suc n) _ (x₁ ∷ env) expr₁)
                  ≤-refl)) ∷ []))

comp-irrelevance : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
  → (n₀ n₁ : ℕ)
  → n₀ < n₁
  → ∀ env expr
  → let (_ , ins) , _ = SSA.ssa1 (compile {A} n env expr) n₁
    in Ignorable A n₀ ins
comp-irrelevance zero n₀ n₁ p env expr = (a<c->¬a≡c n₀ n₁ p) ∷ []
comp-irrelevance (suc n) n₀ n₁ p (x₁ ∷ env) Ind = []
comp-irrelevance (suc n) n₀ n₁ p (x₁ ∷ env) (Lit x₂)
   = comp-irrelevance n n₀ n₁ p env x₂
comp-irrelevance (suc n) n₀ n₁ p (x₁ ∷ env) (Add expr expr₁)
    with comp-irrelevance (suc n) n₀ n₁ p (x₁ ∷ env) expr
... | irre1
    with compHeapInc (suc n) n₁ (x₁ ∷ env) expr
... | heapInc1
    with SSA.ssa1 (compile (suc n) (x₁ ∷ env) expr) n₁
... | (ret1 , ins1) , n₂
    with compHeapInc (suc n) n₂ (x₁ ∷ env) expr₁
... | heapInc2
    with comp-irrelevance (suc n) n₀ n₂ (≤-trans p heapInc1) (x₁ ∷ env) expr₁
... | irre2
    with SSA.ssa1 (compile (suc n) (x₁ ∷ env) expr₁) n₂
... | (ret2 , ins2) , n₃
      = LAll++ irre1 (LAll++ irre2 (a<c->¬a≡c n₀ n₃
          (≤-trans p (≤-trans heapInc1 heapInc2)) ∷ []))
comp-irrelevance (suc n) n₀ n₁ p (x₁ ∷ env) (Sub expr expr₁)
    with comp-irrelevance (suc n) n₀ n₁ p (x₁ ∷ env) expr
... | irre1
    with compHeapInc (suc n) n₁ (x₁ ∷ env) expr
... | heapInc1
    with SSA.ssa1 (compile (suc n) (x₁ ∷ env) expr) n₁
... | (ret1 , ins1) , n₂
    with compHeapInc (suc n) n₂ (x₁ ∷ env) expr₁
... | heapInc2
    with comp-irrelevance (suc n) n₀ n₂ (≤-trans p heapInc1) (x₁ ∷ env) expr₁
... | irre2
    with SSA.ssa1 (compile (suc n) (x₁ ∷ env) expr₁) n₂
... | (ret2 , ins2) , n₃
      = LAll++ irre1 (LAll++ irre2 (a<c->¬a≡c n₀ n₃
          (≤-trans p (≤-trans heapInc1 heapInc2)) ∷ []))
comp-irrelevance (suc n) n₀ n₁ p (x₁ ∷ env) (Mul expr expr₁)
    with comp-irrelevance (suc n) n₀ n₁ p (x₁ ∷ env) expr
... | irre1
    with compHeapInc (suc n) n₁ (x₁ ∷ env) expr
... | heapInc1
    with SSA.ssa1 (compile (suc n) (x₁ ∷ env) expr) n₁
... | (ret1 , ins1) , n₂
    with compHeapInc (suc n) n₂ (x₁ ∷ env) expr₁
... | heapInc2
    with comp-irrelevance (suc n) n₀ n₂ (≤-trans p heapInc1) (x₁ ∷ env) expr₁
... | irre2
    with SSA.ssa1 (compile (suc n) (x₁ ∷ env) expr₁) n₂
... | (ret2 , ins2) , n₃
      = LAll++ irre1 (LAll++ irre2 (a<c->¬a≡c n₀ n₃
          (≤-trans p (≤-trans heapInc1 heapInc2)) ∷ []))
cons-run : ∀ {A} {{num : Num A}} n n₀
   → (es : DChain A n)
   → (rs : Vec Addr n)
   → (h : Heap A)
   → (ins : Ins A)
   → All (λ e → n₀ > e) n rs
   → LAll (λ x → target x ≥ n₀) ins
   → HeapCons h es rs
   → HeapCons (runIns h ins) es rs
cons-run zero n₀ es [] h ins all₁ _ cons = []
cons-run {{num}} (suc n) n₀ (proj₃ , proj₄) (x ∷ rs) h (ins ∷ ins_x) (bg ∷ bgx) (ins_p ∷ ins_px) (cons ∷ consx)
  = (λ num → trans (ignore x (ins ∷ ins_x) (LAll-P (ins_p ∷ ins_px)
        (λ x₁ x₂ → t x (subst (λ a → suc x ≤ a) (sym x₂) (≤-trans bg x₁)))) (<-wf _) h) (cons num))
           ∷ cons-run {{num}} n n₀ proj₄ rs h (ins ∷ ins_x) bgx (ins_p ∷ ins_px) consx
  where
    t : ∀ x → ¬ suc x ≤ x
    t zero = λ ()
    t (suc x₁) (s≤s n) = t x₁ n
cons-run (suc n) n₀ (proj₃ , proj₄) (x ∷ rs) h [] (bg ∷ bgx) [] (cons ∷ consx) = cons ∷ consx

ret<st : ∀ {A} {{num : Num A}} n n₀ env expr → All (λ e → n₀ > e) n env
                             → let (ret , ins) , n₁ =
                                            SSA.ssa1 (compile {A} n env expr) n₀
                               in ret < n₁
ret<st zero n₀ env expr all = ≤-refl
ret<st (suc n) n₀ (x ∷ env) Ind (px ∷ all₁) = px
ret<st (suc n) n₀ (x ∷ env) (Lit x₁) (px ∷ all₁) = ret<st n n₀ env x₁ all₁
ret<st (suc n) n₀ (x ∷ env) (Add expr expr₁) all
    with ret<st (suc n) n₀ (x ∷ env) expr all
... | sta
    with compHeapInc (suc n) n₀ (x ∷ env) expr
... | inc₁
    with SSA.ssa1 (compile (suc n) (x ∷ env) expr) n₀
... | (ret , ins) , n₁
    with ret<st (suc n) n₁ (x ∷ env) expr₁ (allInc inc₁ all)
... | stb
    with SSA.ssa1 (compile (suc n) (x ∷ env) expr₁) n₁
... | (ret2 , ins2) , n₂
    = ≤-refl
ret<st (suc n) n₀ (x ∷ env) (Sub expr expr₁) all
    with ret<st (suc n) n₀ (x ∷ env) expr all
... | sta
    with compHeapInc (suc n) n₀ (x ∷ env) expr
... | inc₁
    with SSA.ssa1 (compile (suc n) (x ∷ env) expr) n₀
... | (ret , ins) , n₁
    with ret<st (suc n) n₁ (x ∷ env) expr₁ (allInc inc₁ all)
... | stb
    with SSA.ssa1 (compile (suc n) (x ∷ env) expr₁) n₁
... | (ret2 , ins2) , n₂
    = ≤-refl
ret<st (suc n) n₀ (x ∷ env) (Mul expr expr₁) all
    with ret<st (suc n) n₀ (x ∷ env) expr all
... | sta
    with compHeapInc (suc n) n₀ (x ∷ env) expr
... | inc₁
    with SSA.ssa1 (compile (suc n) (x ∷ env) expr) n₀
... | (ret , ins) , n₁
    with ret<st (suc n) n₁ (x ∷ env) expr₁ (allInc inc₁ all)
... | stb
    with SSA.ssa1 (compile (suc n) (x ∷ env) expr₁) n₁
... | (ret2 , ins2) , n₂
    = ≤-refl


-- postulate
  -- sem-lem+ : ∀ {A : Set} {{num : Num A}} (n : ℕ)
  --   → (e e₁ : ExprN A (suc n))
  --   → (en : ExprN A n)
  --   → (es : DChain A n)
  --   → let instance ins = toExprNumN {A} n
  --     in Num._+_ num (semantics n (foldExpr id const e en) es)
  --        (semantics n (foldExpr id const e₁ en) es)
  --     ≡
  --     semantics n (((Num._+_ (toExprNumN n)) (foldExpr id const e en))
  --                  (foldExpr id const e₁ en)) es
  -- sem-lem- : ∀ {A : Set} {{num : Num A}} (n : ℕ)
  --   → (e e₁ : ExprN A (suc n))
  --   → (en : ExprN A n)
  --   → (es : DChain A n)
  --   → let instance ins = toExprNumN {A} n
  --     in Num._-_ num (semantics n (foldExpr id const e en) es)
  --        (semantics n (foldExpr id const e₁ en) es)
  --     ≡
  --     semantics n (((Num._-_ (toExprNumN n)) (foldExpr id const e en))
  --                  (foldExpr id const e₁ en)) es
  -- sem-lem* : ∀ {A : Set} {{num : Num A}} (n : ℕ)
  --   → (e e₁ : ExprN A (suc n))
  --   → (en : ExprN A n)
  --   → (es : DChain A n)
  --   → let instance ins = toExprNumN {A} n
  --     in Num._*_ num (semantics n (foldExpr id const e en) es)
  --        (semantics n (foldExpr id const e₁ en) es)
  --     ≡
  --     semantics n (((Num._*_ (toExprNumN n)) (foldExpr id const e en))
  --                  (foldExpr id const e₁ en)) es

comp-sem : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
  → (e : ExprN A n)
  → (es : DChain A n)
  → {h : Heap A}
  → (rs : Vec Addr n) → (r₀ : Addr)
  → HeapCons h es rs
  → All (λ e → r₀ > e) n rs
  → runCompile rs r₀ e h ≡ semantics n e es
comp-sem zero e es rs r₀ hc r₀> = get-put r₀ e _
comp-sem {{num}} (suc n) Ind (en , es) (r ∷ rs) r₀ (c ∷ hc) r₀> = c num
comp-sem (suc n) (Lit e) (en , es) (r ∷ rs) r₀ (_ ∷ hc) (_ ∷ r₀>) =
  comp-sem n e es rs r₀ hc r₀>
comp-sem {A} {{num}} (suc n) (Add e e₁) (en , es) {h} (r ∷ rs) r₀ hc r₀>
    with comp-sem (suc n) e (en , es) (r ∷ rs) r₀ hc r₀>
... | comp-sem₀
    with compHeapInc (suc n) r₀ (r ∷ rs) e
... | inc₁
    with compInsAddrInc (suc n) r₀ (r ∷ rs) e
... | ins-inc₁
    with ret<st (suc n) r₀ (r ∷ rs) e r₀>
... | ret<st₁
    with compile (suc n) (r ∷ rs) e
... | comp₀
    with SSA.ssa1 comp₀ r₀
... | (ret₁ , ins₁) , r₁
    with comp-irrelevance (suc n) ret₁ r₁ ret<st₁ (r ∷ rs) e₁
... | irre
    with comp-sem (suc n) e₁ (en , es) {runIns h ins₁} (r ∷ rs) r₁
           (cons-run (suc n) r₀ (en , es) (r ∷ rs) h ins₁ r₀> ins-inc₁ hc)
           (allInc inc₁ r₀>)
... | comp-sem₁
    with compile (suc n) (r ∷ rs) e₁
... | comp₁
    with SSA.ssa1 comp₁ r₁
... | (ret₂ , ins₂) , r₂
    rewrite runIns-compose ins₁ (ins₂ ++ AddI r₂ ret₁ ret₂ ∷ []) h
          | runIns-compose ins₂ (AddI r₂ ret₁ ret₂ ∷ []) (runIns h ins₁)
          | ignore ret₁ ins₂ irre (<-wf (length ins₂)) (runIns h ins₁)
          | comp-sem₀
          | comp-sem₁
          | (let instance ins = toExprNumN {A} n
             in get-put r₂ ((num Num.+ semantics n (semantics1 {{toExprNumN n}} e en) es)
                    (semantics n (semantics1 {{toExprNumN n}} e₁ en) es))
                      (runIns (runIns h ins₁) ins₂))
         = sym (sem-lem+ n (semantics1 {{toExprNumN n}} e en)
                           (semantics1 {{toExprNumN n}} e₁ en) es)
comp-sem {A} {{num}} (suc n) (Sub e e₁) (en , es) {h} (r ∷ rs) r₀ hc r₀>
    with comp-sem (suc n) e (en , es) (r ∷ rs) r₀ hc r₀>
... | comp-sem₀
    with compHeapInc (suc n) r₀ (r ∷ rs) e
... | inc₁
    with compInsAddrInc (suc n) r₀ (r ∷ rs) e
... | ins-inc₁
    with ret<st (suc n) r₀ (r ∷ rs) e r₀>
... | ret<st₁
    with compile (suc n) (r ∷ rs) e
... | comp₀
    with SSA.ssa1 comp₀ r₀
... | (ret₁ , ins₁) , r₁
    with comp-irrelevance (suc n) ret₁ r₁ ret<st₁ (r ∷ rs) e₁
... | irre
    with comp-sem (suc n) e₁ (en , es) {runIns h ins₁} (r ∷ rs) r₁
             (cons-run (suc n) r₀ (en , es) (r ∷ rs) h ins₁ r₀> ins-inc₁ hc)
             (allInc inc₁ r₀>)
... | comp-sem₁
    with compile (suc n) (r ∷ rs) e₁
... | comp₁
    with SSA.ssa1 comp₁ r₁
... | (ret₂ , ins₂) , r₂
    rewrite runIns-compose ins₁ (ins₂ ++ SubI r₂ ret₁ ret₂ ∷ []) h
          | runIns-compose ins₂ (SubI r₂ ret₁ ret₂ ∷ []) (runIns h ins₁)
          | ignore ret₁ ins₂ irre (<-wf (length ins₂)) (runIns h ins₁)
          | comp-sem₀
          | comp-sem₁
          | (let instance ins = toExprNumN {A} n
             in get-put r₂ ((num Num.- semantics n (semantics1 {{toExprNumN n}} e en) es)
                    (semantics n (semantics1 {{toExprNumN n}} e₁ en) es))
                      (runIns (runIns h ins₁) ins₂))
         = sym (sem-lem- n (semantics1 {{toExprNumN n}} e en)
                           (semantics1 {{toExprNumN n}} e₁ en) es)
comp-sem {A} {{num}} (suc n) (Mul e e₁) (en , es) {h} (r ∷ rs) r₀ hc r₀>
     with comp-sem (suc n) e (en , es) (r ∷ rs) r₀ hc r₀>
... | comp-sem₀
    with compHeapInc (suc n) r₀ (r ∷ rs) e
... | inc₁
     with compInsAddrInc (suc n) r₀ (r ∷ rs) e
... | ins-inc₁
    with ret<st (suc n) r₀ (r ∷ rs) e r₀>
... | ret<st₁
    with compile (suc n) (r ∷ rs) e
... | comp₀
    with SSA.ssa1 comp₀ r₀
... | (ret₁ , ins₁) , r₁
    with comp-irrelevance (suc n) ret₁ r₁ ret<st₁ (r ∷ rs) e₁
... | irre
    with comp-sem (suc n) e₁ (en , es) {runIns h ins₁} (r ∷ rs) r₁
            (cons-run (suc n) r₀ (en , es) (r ∷ rs) h ins₁ r₀> ins-inc₁ hc)
            (allInc inc₁ r₀>)
... | comp-sem₁
    with compile (suc n) (r ∷ rs) e₁
... | comp₁
    with SSA.ssa1 comp₁ r₁
... | (ret₂ , ins₂) , r₂
    rewrite runIns-compose ins₁ (ins₂ ++ MulI r₂ ret₁ ret₂ ∷ []) h
          | runIns-compose ins₂ (MulI r₂ ret₁ ret₂ ∷ []) (runIns h ins₁)
          | ignore ret₁ ins₂ irre (<-wf (length ins₂)) (runIns h ins₁)
          | comp-sem₀
          | comp-sem₁
          | (let instance ins = toExprNumN {A} n
             in get-put r₂ ((num Num.* semantics n (semantics1 {{toExprNumN n}} e en) es)
                    (semantics n (semantics1 {{toExprNumN n}} e₁ en) es))
                      (runIns (runIns h ins₁) ins₂))
         = sym (sem-lem* n (semantics1 {{toExprNumN n}} e en)
                           (semantics1 {{toExprNumN n}} e₁ en) es)
  

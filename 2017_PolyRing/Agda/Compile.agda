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

runSSA : ∀ {A : Set} {{_ : Num A}} {n : ℕ}
       → SSA (Addr × Ins A) → Addr → Heap A → A
runSSA (ssa m) r₀ h =
  let ((r , ins) , _) = m r₀
  in getHeap r (runIns h ins)

runCompile : ∀ {A : Set} {{_ : Num A}} {n : ℕ}
           → Vec Addr n → Addr → ExprN A n → Heap A → A
runCompile {n = n} rs r₀ e h =
   runSSA {n = n} (compile n rs e) r₀ h

data HeapCons {A : Set} (h : Heap A) :
        ∀ {n : ℕ} → Nest A n → Vec Addr n → Set where
  [] : HeapCons h tt []
  _∷_ : ∀ {n : ℕ} {es rs e r} {num : Num A}
         → ((num : Num A) → getHeap r h ≡ semantics {{num}} n e es)
         → HeapCons h {n} es rs
         → HeapCons h (e , es) (r ∷ rs)
data All {a b} {A : Set a}
         (P : A → Set b) : (n : ℕ) → Vec A n → Set (a ⊔ b) where
  [] : All P 0 []
  _∷_ : ∀ {n x xs} (px : P x) (pxs : All P n xs) → All P (suc n) (x ∷ xs)

data LAll {a b} {A : Set a}
          (P : A → Set b) : List A → Set (a ⊔ b) where
  [] : LAll P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : LAll P xs) → LAll P (x ∷ xs)

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
  

mutual
 comp-sem : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
   → (e : ExprN A n)
   → (es : Nest A n)
   → {h : Heap A}
   → (rs : Vec Addr n) → (r₀ : Addr)
   → HeapCons h es rs
   → All (λ e → r₀ > e) n rs
   → runCompile rs r₀ e h ≡ semantics n e es
 comp-sem zero e es rs r₀ hc r₀> = get-put r₀ e _
 comp-sem {A} (suc n) e (en , es) (r ∷ rs) r₀ hc r₀> = comp-sem' n e en es r rs r₀ hc r₀>

 comp-sem' : ∀ {A : Set} {{num : Num A}} (n : ℕ)
           → (e : Expr (ExprN A n))
           → (en : ExprN A n) (es : Nest A n)
           → {h : Heap A}
           → (r : Addr) → (rs : Vec Addr n) → (r₀ : Addr)
           → HeapCons h (en , es) (r ∷ rs)
           → All (λ e → r₀ > e) (suc n) (r ∷ rs)
           → runSSA {n = n} (compile (suc n) (r ∷ rs) e) r₀ h ≡
                     semantics n (semantics1 {{toExprNumN n}} e en) es
 comp-sem' {{num}} n Ind en es r rs r₀ (c ∷ hc) r₀> = c num
 comp-sem' n (Lit e) en es r rs r₀ (_ ∷ hc) (_ ∷ r₀>) =
   comp-sem n e es rs r₀ hc r₀>
 comp-sem' n (Add e e₁) en es {h} r rs r₀ hc r₀>
     with comp-sem' n e en es r rs r₀ hc r₀>
 ... | comp-sem₀
     with comp-sem' n e₁ en es r rs r₀ hc r₀>
 ... | comp-sem₁
     with compile (suc n) (r ∷ rs) e
 ... | comp₀
     with SSA.ssa1 comp₀ r₀
 ... | (ret₁ , ins₁) , r₁
     with compile (suc n) (r ∷ rs) e₁
 ... | comp₁
     with SSA.ssa1 comp₁ r₁
 ... | (ret₂ , ins₂) , r₂
     rewrite runIns-compose ins₁ (ins₂ ++ AddI r₂ ret₁ ret₂ ∷ []) h
           | runIns-compose ins₂ (AddI r₂ ret₁ ret₂ ∷ []) (runIns h ins₁)
           | ignore ret₁ ins₂ {!!} (<-wf (length ins₂)) (runIns h ins₁)
           = {!!}
 comp-sem' n (Sub e e₁) en es r rs r₀ hc r₀> = {!!}
 comp-sem' n (Mul e e₁) en es r rs r₀ hc r₀> = {!!}

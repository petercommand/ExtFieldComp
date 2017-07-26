module Compile where

open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (_⊔_)
open import Data.List
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
  no-eta-equality
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
compile {A} (suc n) (x ∷ addr) exp
    rewrite numEquiv A n
  = foldExpr (pass x) (compile n addr) exp

-- running a program

postulate
  Heap : Set → Set
postulate
  putHeap : ∀ {A : Set} → Addr → A → Heap A → Heap A
  getHeap : ∀ {A : Set} → Addr → Heap A → A
  get-put : ∀ {A : Set} → ∀ c (k : A) h → getHeap c (putHeap c k h) ≡ k
  get-put' : ∀ {A : Set} → ∀ c c' (k : A) h → ¬ c ≡ c'
                         → getHeap c (putHeap c' k h) ≡ getHeap c h


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

mutual
 comp-sem : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
   → (e : ExprN A n)
   → (es : Nest A n)
   → {h : Heap A}
   → (rs : Vec Addr n) → (r₀ : Addr)  -- additional constraint needed
   → HeapCons h es rs
   → runCompile rs r₀ e h ≡ semantics n e es
 comp-sem zero e es rs r₀ hc = get-put r₀ e _
 comp-sem {A} (suc n) e (en , es) (r ∷ rs) r₀ hc rewrite numEquiv A n =
   comp-sem' n e en es r rs r₀ hc

 comp-sem' : ∀ {A : Set} {{num : Num A}} (n : ℕ)
           → (e : Expr (ExprN A n))
           → (en : ExprN A n) (es : Nest A n)
           → {h : Heap A}
           → (r : Addr) → (rs : Vec Addr n) → (r₀ : Addr)  -- additional constraint needed
           → HeapCons h (en , es) (r ∷ rs)
           → runSSA {n = n} (foldExpr (pass r) (compile n rs) e) r₀ h ≡
                     semantics n (semantics1 {{toExprNumN n}} e en) es
 comp-sem' {{num}} n Ind en es r rs rₒ (c ∷ hc) = c num
 comp-sem' n (Lit e) en es r rs rₒ (_ ∷ hc) =
   comp-sem n e es rs rₒ hc
 comp-sem' n (Add e e₁) en es r rs rₒ hc = {!   !}
 comp-sem' n (Sub e e₁) en es r rs rₒ hc = {!   !}
 comp-sem' n (Mul e e₁) en es r rs rₒ hc = {!   !}

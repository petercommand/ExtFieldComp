open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Nat hiding (_⊔_)
open import Data.Bool hiding (_≟_)
open import Data.Fin hiding (_≤_; _+_; _<_)
open import Data.List
open import Data.Vec hiding (_>>=_) renaming (_++_ to _v++_)
open import Num
open import NatProperties
open import Data.Nat.Properties.Simple
open import Level hiding (zero; suc)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (setoid; inspect)
open ≡-Reasoning

-- Non-Dependent Pair
record _×_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public
infixr 2 _×_
infixr 4 _,_

--

data All {a p} {A : Set a}
         (P : A → Set p) : (n : ℕ) → Vec A n → Set (p ⊔ a) where
  A[] : All P 0 []
  _A∷_ : ∀ {n x xs} (px : P x) (pxs : All P n xs) → All P (suc n) (x ∷ xs)



--
data Expr {l} (A : Set l) : Set l where
  Ind : Expr A
  Lit : (x : A) -> Expr A
  Add : (e1 : Expr A) -> (e2 : Expr A) -> Expr A
  Sub : (e1 : Expr A) -> (e2 : Expr A) -> Expr A
  Mul : (e1 : Expr A) -> (e2 : Expr A) -> Expr A


module _ where
  -- abstract
  
  foldExpr : ∀ {m} {a : Set m} {b : Set} {{num : Num b}}
           -> b
           -> (a -> b)
           -> Expr a
           -> b
  foldExpr x f Ind = x
  foldExpr _ f (Lit x) = f x
  foldExpr {{num}} x f (Add e1 e2) =
     let _+_ = Num._+_ num
     in foldExpr x f e1 + foldExpr x f e2
  foldExpr {{num}} x f (Sub e1 e2) =
     let _-_ = Num._-_ num
     in foldExpr x f e1 - foldExpr x f e2
  foldExpr {{num}} x f (Mul e1 e2) =
     let _*_ = Num._*_ num
     in foldExpr x f e1 * foldExpr x f e2
  foldExpr-Ind-elim : ∀ {m} (a : Set m) {b : Set} {{num : Num b}}
          -> (x : b)
          -> (f : (a -> b))
          -> foldExpr x f Ind ≡ x
  foldExpr-Ind-elim a x f = refl
  foldExpr-Lit-elim : ∀ {m} {a : Set m} {b : Set} {{num : Num b}}
          -> (t : b)
          -> (f : (a -> b))
          -> (x : a)
          -> foldExpr t f (Lit x) ≡ f x
  foldExpr-Lit-elim t f x = refl
  foldExpr-Add-elim : ∀ {m} (a : Set m) {b : Set} {{num : Num b}}
          -> (x : b)
          -> (f : (a -> b))
          -> (e1 e2 : Expr a)
          -> let _+_ = Num._+_ num
             in foldExpr x f (Add e1 e2) ≡ foldExpr x f e1 + foldExpr x f e2
  foldExpr-Add-elim a x f e1 e2 = refl
  foldExpr-Sub-elim : ∀ {m} (a : Set m) {b : Set} {{num : Num b}}
          -> (x : b)
          -> (f : (a -> b))
          -> (e1 e2 : Expr a)
          -> let _-_ = Num._-_ num
             in foldExpr x f (Sub e1 e2) ≡ foldExpr x f e1 - foldExpr x f e2
  foldExpr-Sub-elim a x f e1 e2 = refl
  foldExpr-Mul-elim : ∀ {m} (a : Set m) {b : Set} {{num : Num b}}
          -> (x : b)
          -> (f : (a -> b))
          -> (e1 e2 : Expr a)
          -> let _*_ = Num._*_ num
             in foldExpr x f (Mul e1 e2) ≡ foldExpr x f e1 * foldExpr x f e2
  foldExpr-Mul-elim a x f e1 e2 = refl
    
ExprN : ∀ {l} (A : Set l) (n : ℕ) -> Set l
ExprN A zero = A
ExprN A (suc n) = Expr (ExprN A n)

Expr2 : ∀ {l} (A : Set l) -> Set l
Expr2 A = ExprN A (suc (suc zero))

Nest : Set -> ℕ -> Set
Nest A zero = ⊤
Nest A (suc n) = ExprN A n × Nest A n
              
instance toFuncNum : ∀ {A : Set} (num : Num A) -> Num (A -> A)
toFuncNum record { _+_ = _+_ ; _-_ = _-_ ; _*_ = _*_ }
   = record { _+_ = \f g x -> f x + g x
            ; _-_ = \f g x -> f x - g x
            ; _*_ = \f g x -> f x * g x
            }

instance toExprNum : ∀ {A : Set} (num : Num A) -> Num (Expr A)
toExprNum record { _+_ = _+_ ; _-_ = _-_ ; _*_ = _*_ }
   = record { _+_ = \e1 e2 -> Add e1 e2
            ; _-_ = \e1 e2 -> Sub e1 e2
            ; _*_ = \e1 e2 -> Mul e1 e2
            }
fmap : ∀ {A B : Set} -> (A -> B) -> Expr A -> Expr B
fmap f Ind = Ind
fmap f (Lit x) = Lit (f x)
fmap f (Add e e₁) = Add (fmap f e) (fmap f e₁)
fmap f (Sub e e₁) = Sub (fmap f e) (fmap f e₁)
fmap f (Mul e e₁) = Mul (fmap f e) (fmap f e₁)

numEquiv : ∀ (A : Set) (n : ℕ) -> Expr (ExprN A n) ≡ ExprN (Expr A) n 
numEquiv _ zero = refl
numEquiv _ (suc n) = cong Expr (numEquiv _ n)

{-
exprLift : ∀ {l} {A : Set l} m n -> m ≤ n -> ExprN A m -> ExprN A n
exprLift _ zero z≤n exp = exp
exprLift zero (suc n) z≤n exp = exprLift 0 n z≤n (Lit exp)
exprLift (suc m) (suc n) (s≤s p) exp = exprLift m n p exp
-}

compose : ∀ {A : Set} -> (n : ℕ) -> (A -> A) -> (A -> A)
compose zero f = id
compose (suc n) f = f ∘ compose n f

fmapN : ∀ {A : Set}{m} -> (n : ℕ) -> (ExprN A m -> ExprN A m) -> ExprN A (m + n) -> ExprN A (m + n)
fmapN {_} {m} zero f rewrite +-comm m zero = f
fmapN {A} {m} (suc n) f rewrite a+suc-b==suc-a+b m n
   = fmapN {_} {suc m} n (fmap f)

toExprNumN : ∀ {A : Set} (n : ℕ){{num : Num A}} -> Num (ExprN A n)
toExprNumN zero {{num}} = num
toExprNumN {A} (suc n) {{num}} = toExprNum (toExprNumN n)

semantics1 : ∀ {A : Set} {{num : Num A}} → Expr A → A → A
semantics1 = foldExpr id const


semantics : ∀ {A : Set}{{num : Num A}} (n : ℕ) → (exp : ExprN A n) → Nest A n → A
semantics zero x tt = x
semantics {A} (suc n) e (t , es)
    = let instance ins = toExprNumN n
      in semantics n (semantics1 e t) es

record Addr : Set where
  constructor [[_]]
  field
    addr : ℕ

open Addr
data TAC (A : Set) : Set where
  ConstI : Addr -> A -> TAC A
  AddI : Addr -> Addr -> Addr -> TAC A
  SubI : Addr -> Addr -> Addr -> TAC A
  MulI : Addr -> Addr -> Addr -> TAC A

Ins : Set -> Set
Ins A = List (TAC A)



record SSA (A : Set) (B : Set) : Set where
--  no-eta-equality
  constructor ssa
  field
    ssa1 : Addr -> B × Addr



return : ∀ {S A : Set} → A → SSA S A
return a = ssa (λ x → a , x)

_>>=_ : ∀ {S A B : Set} → SSA S A → (A → SSA S B) → SSA S B
ssa x >>= f = ssa (λ args → let r , s = x args
                                ssa s' = f r
                            in s' s)
infixr 10 _>>=_

do_ : ∀ {a} {A : Set a} → A → A
do x = x

infixr 0 do-bind
syntax do-bind m (λ x → m₁) = x ← m -| m₁
do-bind = _>>=_


getvar : ∀ {A : Set} → SSA A Addr
getvar = ssa (λ args → let [[ n ]] = args
                       in [[ n ]] , [[ suc n ]])

biOpSSA : ∀ {A : Set}
          → (Addr -> Addr -> Addr -> TAC A)
          → SSA A (Addr × Ins A) → SSA A (Addr × Ins A)
          → SSA A (Addr × Ins A)
biOpSSA op p1 p2
  = p1 >>= λ x →
    p2 >>= λ y →
    getvar >>= λ dest →
    let (addr1 , ins1) = x
        (addr2 , ins2) = y
    in return (dest , ins1 ++ ins2 ++ (op dest addr1 addr2 ∷ []))

instance SSANum : ∀ {A : Set} -> Num (SSA A (Addr × Ins A))
SSANum = record { _+_ = biOpSSA AddI
                ; _-_ = biOpSSA SubI
                ; _*_ = biOpSSA MulI }
pass : ∀ {A B : Set} → A → SSA B (A × Ins B)
pass r = return (r , [])

compile0 : ∀ {A : Set} → A → SSA A (Addr × List (TAC A))
compile0 v = getvar >>= λ addr →
             return (addr , ConstI addr v ∷ [])
-- abstract
compile : ∀ {A : Set} (n : ℕ) → Vec Addr n
   → ExprN A n → SSA A (Addr × Ins A)
compile zero addr exp = compile0 exp
compile {A} (suc n) (x ∷ addr) exp
  = foldExpr (pass x) (compile n addr) exp

compile-base-elim : ∀ (A : Set)
    → (exp : A)
    → compile 0 [] exp ≡ compile0 exp
compile-base-elim A exp = refl

compile-ind-elim : ∀ (A : Set) (n : ℕ)
    → (x : Addr)
    → (addr : Vec Addr n)
    → (exp : ExprN A (suc n))
    → compile (suc n) (x ∷ addr) exp ≡
      foldExpr (pass x) (compile n addr) exp
compile-ind-elim A n x addr exp = refl
-- abstract end
{-
compileEnv : ∀ {A : Set} (n : ℕ) → Nest A n → SSA A (Vec Addr n × Ins A)
compileEnv zero nest = return (Vec.[] , [])
compileEnv {A} (suc n) (proj₁ , proj₂)
  = compileEnv n proj₂ >>= λ k →
    let addr , ins = k
    in compile n addr proj₁ >>= λ k1 →
    let addr1 , ins2 = k1
    in return (subst id (sym (trans (cong (λ x → Vec Addr (suc x))
                                       (sym (zero-red {n})))
                                    (cong (λ x → Vec Addr x) (sym (a+suc-b==suc-a+b n 0)))))
                (addr v++ (addr1 ∷ [])) , ins ++ ins2)
  
compAll : ∀ {A : Set} (n : ℕ) → Nest A n → ExprN A n → SSA A (Addr × Ins A)
compAll n env exp = compileEnv n env >>= λ k →
                    let env_e , ins_e = k
                    in compile n env_e exp >>= λ k1 →
                    let ret , ins_e2 = k1
                    in return (ret , ins_e ++ ins_e2)
-}
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

runIns-compose : ∀ {A : Set} {{_ : Num A}} (ins1 ins2 : Ins A) (h : Heap A)
  → runIns h (ins1 ++ ins2) ≡ runIns (runIns h ins1) ins2
runIns-compose [] ins2 h = refl
runIns-compose (ConstI x₁ x₂ ∷ ins1) ins2 h = runIns-compose ins1 ins2 _
runIns-compose (AddI x₁ x₂ x₃ ∷ ins1) ins2 h = runIns-compose ins1 ins2 _
runIns-compose (SubI x₁ x₂ x₃ ∷ ins1) ins2 h = runIns-compose ins1 ins2 _
runIns-compose (MulI x₁ x₂ x₃ ∷ ins1) ins2 h = runIns-compose ins1 ins2 _

runSSA : ∀ {A : Set} {{_ : Num A}} → SSA A (Addr × Ins A) → Addr → Heap A → A
runSSA (ssa ssa1) addr h
  = let r , _ = ssa1 addr
        addr , ins = r
    in getHeap addr (runIns h ins) 

-- splitEnv' : ∀ {A : Set} (i n : ℕ) → Nest A n → Nest A (suc i)

suc-⊥ : ∀ i → suc i ≤ i → ⊥
suc-⊥ zero ()
suc-⊥ (suc i) (s≤s p) = suc-⊥ i p

splitEnv : ∀ {A : Set} (i n : ℕ) → i ≤ n → Nest A n → Nest A i
splitEnv zero n p e = tt
splitEnv (suc i) zero () e
splitEnv (suc i) (suc n) p e with i ≟ n
splitEnv {A} (suc i) (suc n) p₁ e | yes p = subst (λ x → ExprN A x × Nest A x) (sym p) e
splitEnv (suc i) (suc n) (s≤s p) (e₁ , e₂) | no ¬p = splitEnv (suc i) n (neq-le i n p ¬p) e₂

_!_ : ∀ {l} {A : Set l} {n : ℕ} → Vec A n → (i : ℕ) → i < n → A
([] ! zero) ()
((x ∷ vec) ! zero) (s≤s p) = x
([] ! suc i) ()
((x ∷ vec) ! suc i) (s≤s p) = (vec ! i) p


!-proof-irrelevance : ∀ {l} {A : Set l} {n : ℕ} → (vec : Vec A n) → (i : ℕ) → ∀ (p p₁ : i < n) → (vec ! i) p ≡ (vec ! i) p₁
!-proof-irrelevance [] zero () p₁
!-proof-irrelevance [] (suc _) () p₁
!-proof-irrelevance (x ∷ vec) zero (s≤s p) (s≤s p₁) = refl
!-proof-irrelevance (x ∷ vec) (suc i) (s≤s p) (s≤s p₁) = !-proof-irrelevance vec i p p₁

aux'' : ∀ n i p → ℕ- n (suc i) p < n
aux'' zero zero ()
aux'' (suc n) zero (s≤s p) rewrite ℕ-0 n p = ≤-refl
aux'' zero (suc i) ()
aux'' (suc n) (suc i) (s≤s p) = s≤s (≤weak (aux'' n i p))

aux' : ∀ {A : Set} (n : ℕ) → (x : A) → (env₀ : Vec A n) → (w : ℕ) → (p : w ≡ 0) → (p₂ : w ≤ n) → ((x ∷ env₀) ! w) (s≤s p₂) ≡ x
aux' n x env₀ zero p p₂ = refl
aux' n x env₀ (suc w) () p₂

aux : ∀ {A : Set} (n : ℕ) → (x : A) → (env₀ : Vec A n) → ∀ p → ((x ∷ env₀) ! (ℕ- n n ≤-refl)) p ≡ x
aux n x env (s≤s p) = aux' n x env (ℕ- n n ≤-refl) (ℕ-refl n ≤-refl) p

cons₀ : ∀ (n i : ℕ) p → (x : Addr)
            → (env₀ : Vec Addr n)
            → ((x ∷ env₀) ! ℕ- n i (≤weak p)) (aux'' (suc n) i (s≤s (≤weak p))) ≡
              (env₀ ! ℕ- n (suc i) p) (aux'' n i p)
cons₀ zero i () x env₀
cons₀ (suc n) i (s≤s p) x env₀ with ℕ- (suc n) i (≤weak (s≤s p))
                                  | ℕ- n i p
                                  | aux'' (suc (suc n)) i (s≤s (≤weak (s≤s p)))
                                  | aux'' (suc n) i (s≤s p)
                                  | ℕ--suc' n i (≤weak (s≤s p)) p
... | a | b | s≤s c | d | refl = !-proof-irrelevance env₀ b c d


≤-bot : ∀ n → suc n ≤ n → ⊥
≤-bot zero ()
≤-bot (suc n) (s≤s p) = ≤-bot n p

splitEnv-proof-irrelevance : ∀ {A : Set} (n i : ℕ) →
    ∀ (e : Nest A n) p₁ p₂ → splitEnv i n p₁ e ≡ splitEnv i n p₂ e
splitEnv-proof-irrelevance n zero e p₁ p₂ = refl
splitEnv-proof-irrelevance zero (suc i) e () p₂
splitEnv-proof-irrelevance (suc n) (suc i) e p₁ p₂ with i ≟ n
splitEnv-proof-irrelevance (suc n) (suc .n) e p₁ p₂ | yes refl = refl
splitEnv-proof-irrelevance (suc n) (suc i) (proj₃ , proj₄) (s≤s p₁) (s≤s p₂) | no ¬p
  = splitEnv-proof-irrelevance n (suc i) proj₄ (neq-le i n p₁ ¬p) (neq-le i n p₂ ¬p)

splitEnv-weaken : ∀ {A : Set} (n i : ℕ) → ∀ p₁ p₂ (e_n : ExprN A n) (e_sn : Nest A n)
   → splitEnv (suc i) (suc n) p₁ (e_n , e_sn) ≡ splitEnv (suc i) n p₂ e_sn
splitEnv-weaken zero i (s≤s p₁) () e_n e_sn
splitEnv-weaken (suc n) zero (s≤s p₁) p₂ e_n e_sn with n ≟ 0
splitEnv-weaken (suc .0) zero (s≤s p₁) p₂ e_n e_sn | yes refl = refl
splitEnv-weaken (suc n) zero (s≤s p₁) (s≤s z≤n) e_n e_sn | no ¬p = refl
splitEnv-weaken (suc n) (suc i) (s≤s (s≤s p₁)) (s≤s p₂) e_n (proj₃ , proj₄) with i ≟ n
splitEnv-weaken (suc .i) (suc i) (s≤s (s≤s p₁)) (s≤s p₂) e_n (proj₃ , proj₄) | yes refl with suc i ≟ i
splitEnv-weaken (suc .(suc _)) (suc .(suc _)) (s≤s (s≤s p₁)) (s≤s (s≤s p₂)) e_n (proj₃ , proj₄) | yes refl | (yes ())
splitEnv-weaken (suc .(suc _)) (suc .(suc _)) (s≤s (s≤s p₁)) (s≤s (s≤s p₂)) e_n (proj₃ , proj₄) | yes refl | (no ¬p) = ⊥-elim (≤-bot _ p₂)
splitEnv-weaken (suc n) (suc i) (s≤s (s≤s p₁)) (s≤s p₂) e_n (proj₃ , proj₄) | no ¬p with suc i ≟ n
splitEnv-weaken (suc n) (suc i) (s≤s (s≤s p₁)) (s≤s p₂) e_n (proj₃ , proj₄) | no ¬p | (yes p) = refl
splitEnv-weaken (suc n) (suc i) (s≤s (s≤s p₁)) (s≤s p₂) e_n (proj₃ , proj₄) | no ¬p₁ | (no ¬p)
   = splitEnv-proof-irrelevance n (suc (suc i)) proj₄ (neq-le (suc i) n
       (neq-le i n p₁
        (λ x → ¬p₁ (subst (λ x₁ → i ≡ Data.Nat.pred x₁) (cong suc x) refl))) ¬p) (neq-le (suc i) n p₂ ¬p)

cons-weaken : ∀ {A : Set} {{_ : Num A}} {n : ℕ} {x : Addr} {env₀ : Vec Addr n} {e_n : ExprN A n} {e_sn : Nest A n} {h : Heap A}
    → (c : (i : ℕ) (p : i < suc n) →
           getHeap (((x ∷ env₀) ! ℕ- (suc n) (1 + i) p) (aux'' (suc n) i p)) h
         ≡
           semantics i (proj₁ (splitEnv (suc i) (suc n) p (e_n , e_sn)))
             (proj₂ (splitEnv (suc i) (suc n) p (e_n , e_sn))))
    → (i : ℕ) (p : i < n) →
      getHeap ((env₀ ! ℕ- n (1 + i) p) (aux'' n i p)) h ≡
      semantics i (proj₁ (splitEnv (suc i) n p e_sn))
      (proj₂ (splitEnv (suc i) n p e_sn))
cons-weaken {A} {{_}} {n} {x} {env₀} {e_n} {e_sn} {h} c i p =
  trans (trans (cong (λ k → getHeap k h) (sym (cons₀ n i p x env₀))) (c i (≤-suc (suc i) n p)))
     (subst (λ x → semantics i (proj₁ x) (proj₂ x)
                    ≡
                   semantics i (proj₁ (splitEnv (suc i) n p e_sn))
                     (proj₂ (splitEnv (suc i) n p e_sn))) (sym (splitEnv-weaken n i (s≤s (≤weak p)) p e_n e_sn)) refl)



comp-sem : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
  → (exp : ExprN A n)
  → (env : Nest A n)
  → (env₀ : Vec Addr n)
  → (h : Heap A)
  → (n₀ : ℕ)
  → All (λ e → n₀ > addr e) n env₀
  → (∀ (i : ℕ) → (p : i < n) → let eᵢ , envᵢ = splitEnv (suc i) n p env
                               in getHeap ((env₀ ! (ℕ- n (1 + i) p)) (aux'' n i p)) h ≡ semantics i eᵢ envᵢ)
  → runSSA (compile n env₀ exp) [[ n₀ ]] h ≡ semantics n exp env
comp-sem {A} zero exp env [] h n₀ n₀p cons 
   = begin runSSA (compile 0 [] exp) [[ n₀ ]] h
        ≡⟨ cong (λ x → runSSA x [[ n₀ ]] h) (compile-base-elim A exp) ⟩
           getHeap [[ n₀ ]] (putHeap [[ n₀ ]] exp h)
        ≡⟨ get-put [[ n₀ ]] exp h ⟩
           refl
comp-sem {A} {{num}} (suc n) Ind (e_n , e_sn) (x ∷ env₀) h n₀ n₀p cons with cons n ≤-refl
comp-sem {A} {{num}} (suc n) Ind (e_n , e_sn) (x ∷ env₀) h n₀ n₀p cons | c₁ with n ≟ n
comp-sem {A} {{num}} (suc n) Ind (e_n , e_sn) (x ∷ env₀) h n₀ n₀p cons | c₁ | yes refl =
     let instance ins = toExprNumN {A} n
     in
      begin runSSA {{num}} (compile (suc n) (x ∷ env₀) Ind) [[ n₀ ]] h
         ≡⟨ cong (λ x → runSSA {{num}} x [[ n₀ ]] h) (compile-ind-elim A n x env₀ Ind) ⟩
           runSSA {{num}} (foldExpr (pass x) (compile n env₀) Ind) [[ n₀ ]] h
         ≡⟨ cong (λ x → runSSA {{num}} x [[ n₀ ]] h)
                   (foldExpr-Ind-elim (ExprN A n) (pass x) (compile n env₀)) ⟩
 sym  (begin semantics {{num}} n (semantics1 Ind e_n) e_sn
          ≡⟨ cong (λ x → semantics {{num}} n x e_sn) (cong (λ x → x e_n) (foldExpr-Ind-elim (ExprN A n) id const)) ⟩
             semantics n e_n e_sn
          ≡⟨ sym c₁ ⟩
             getHeap (((x ∷ env₀) ! ℕ- n n ≤-refl) (aux'' (suc n) n (s≤s ≤-refl))) h
          ≡⟨ cong (λ k → getHeap k h) (aux n x env₀ (aux'' (suc n) n (s≤s ≤-refl))) ⟩
             getHeap x h
          ∎
  )
comp-sem {A} {{num}} (suc n) Ind (e_n , e_sn) (x ∷ env₀) h n₀ n₀p cons | c₁ | no ¬p' = ⊥-elim (¬p' refl)
comp-sem {A} (suc n) (Lit x₁) (e_n , e_sn) (x ∷ env₀) h n₀ (n₀p A∷ n₀px) cons =
     let instance ins = toExprNumN {A} n
     in
   begin runSSA (compile (suc n) (x ∷ env₀) (Lit x₁)) [[ n₀ ]] h
      ≡⟨ cong (λ x → runSSA x [[ n₀ ]] h) (compile-ind-elim A n x env₀ (Lit x₁)) ⟩
         runSSA (foldExpr (pass x) (compile n env₀) (Lit x₁)) [[ n₀ ]] h
      ≡⟨ cong (λ x → runSSA x [[ n₀ ]] h) (foldExpr-Lit-elim (pass x) (compile n env₀) x₁) ⟩
         runSSA (compile n env₀ x₁) [[ n₀ ]] h
      ≡⟨ comp-sem n x₁ e_sn env₀ h n₀ n₀px (cons-weaken cons) ⟩
         semantics n x₁ e_sn
      ≡⟨ sym (cong (λ x → semantics n (x e_n) e_sn) (foldExpr-Lit-elim id const x₁)) ⟩
         semantics n (semantics1 (Lit x₁) e_n) e_sn
      ∎
comp-sem {A} (suc n) (Add exp exp₁) (e_n , e_sn) (x ∷ env₀) h n₀ n₀p cons
    with comp-sem (suc n) exp (e_n , e_sn) (x ∷ env₀) h n₀ n₀p cons
... | comp_sem₁
    with compile (suc n) (x ∷ env₀) exp
... | comp1
    with SSA.ssa1 comp1 [[ n₀ ]]
... | (ret1 , ins1) , [[ n₁ ]]
    with comp-sem (suc n) exp (e_n , e_sn) (x ∷ env₀) h n₁ {!!} cons
... | comp_sem₂
    with compile (suc n) (x ∷ env₀) exp₁
... | comp2
    with SSA.ssa1 comp2 [[ n₁ ]]
... | (ret2 , ins2) , [[ n₂ ]]
    rewrite runIns-compose ins1 (ins2 ++ AddI [[ n₂ ]] ret1 ret2 ∷ []) h
          | runIns-compose ins2 (AddI [[ n₂ ]] ret1 ret2 ∷ []) (runIns h ins1)
    = {!!}
{-
   begin runSSA (compile (suc n) (x ∷ env₀) (Add exp exp₁)) [[ n₀ ]] h
      ≡⟨ cong (λ k → runSSA k [[ n₀ ]] h) (compile-ind-elim A n x env₀ (Add exp exp₁)) ⟩
         runSSA (foldExpr (pass x) (compile n env₀) (Add exp exp₁)) [[ n₀ ]] h
      ≡⟨ cong (λ k → runSSA k [[ n₀ ]] h) (foldExpr-Add-elim (ExprN A n) (pass x) (compile n env₀) exp exp₁) ⟩
         {!!} -}
comp-sem {A} (suc n) (Sub exp exp₁) env env₀ h n₀ n₀p cons = {!!}
comp-sem {A} (suc n) (Mul exp exp₁) env env₀ h n₀ n₀p cons = {!!}

idExpr2 : ∀ {A : Set} {{num : Num A}} → Expr2 A → Expr2 A
idExpr2 = foldExpr {{toExprNumN 2}} Ind
            (foldExpr {{toExprNumN 2}} (Lit Ind) (Lit ∘ Lit))

rotaExpr2 : ∀ {A : Set} {{num : Num A}} → Expr2 A → Expr2 A
rotaExpr2 = foldExpr {{toExprNumN 2}} (Lit Ind)
              (foldExpr {{toExprNumN 2}} Ind (Lit ∘ Lit))

rotaExprN : ∀ {A : Set} {{num : Num A}} (n : ℕ) → ExprN A n → ExprN A n
rotaExprN zero = id
rotaExprN (suc zero) = id
rotaExprN (suc (suc zero)) = rotaExpr2
rotaExprN (suc (suc (suc n))) = {!!} -- fmapN {_} {1} (suc n) rotaExpr2 ∘ rotaExprN {{toExprNumN 1}} (suc (suc n))



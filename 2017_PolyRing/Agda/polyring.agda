open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (_≤_; _+_; _<_)
open import Data.List
open import Data.Vec hiding (_>>=_) renaming (_++_ to _v++_)
open import Num
open import NatProperties
open import Data.Nat.Properties.Simple
open import Level hiding (zero; suc)
open import Function
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
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


data Expr {l} (A : Set l) : Set l where
  Ind : Expr A
  Lit : (x : A) -> Expr A
  Add : (e1 : Expr A) -> (e2 : Expr A) -> Expr A
  Sub : (e1 : Expr A) -> (e2 : Expr A) -> Expr A
  Mul : (e1 : Expr A) -> (e2 : Expr A) -> Expr A

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


ExprN : ∀ {l} (A : Set l) (n : ℕ) -> Set l
ExprN A zero = A
ExprN A (suc n) = ExprN (Expr A) n

Expr2 : ∀ {l} (A : Set l) -> Set l
Expr2 A = ExprN A (suc (suc zero))

Nest : Set -> ℕ -> Set
Nest A zero = ⊤
Nest A (suc n) = ExprN A n × Nest A n

NestRange : Set -> (st : ℕ) -> (len : ℕ) -> Set
NestRange A _ zero = ⊤
NestRange A zero (suc len) = ⊤
NestRange A (suc st) (suc len)
   = ExprN A st × NestRange A st len
              
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

numEquiv : ∀ (A : Set) (n : ℕ) -> ExprN (Expr A) n ≡ Expr (ExprN A n)
numEquiv _ zero = refl
numEquiv _ (suc n) = numEquiv _ n

exprLift : ∀ {l} {A : Set l} m n -> m ≤ n -> ExprN A m -> ExprN A n
exprLift _ zero z≤n exp = exp
exprLift zero (suc n) z≤n exp = exprLift 0 n z≤n (Lit exp)
exprLift (suc m) (suc n) (s≤s p) exp = exprLift m n p exp

compose : ∀ {A : Set} -> (n : ℕ) -> (A -> A) -> (A -> A)
compose zero f = id
compose (suc n) f = f ∘ compose n f

fmapN : ∀ {A : Set}{m} -> (n : ℕ) -> (ExprN A m -> ExprN A m) -> ExprN A (m + n) -> ExprN A (m + n)
fmapN {_} {m} zero f rewrite +-comm m zero = f
fmapN {A} {m} (suc n) f rewrite a+suc-b==suc-a+b m n
   = fmapN {_} {suc m} n (subst (\x -> x -> x) (sym $ numEquiv A m) (fmap f))

toExprNumN : ∀ {A : Set} (n : ℕ){{num : Num A}} -> Num (ExprN A n)
toExprNumN zero {{num}} = num
toExprNumN {A} (suc n) {{num}} rewrite numEquiv A n =
   toExprNum (toExprNumN n)

semantics1 : ∀ {A : Set} {{num : Num A}} → Expr A → A → A
semantics1 = foldExpr id const

{-
semantics : ∀ {A : Set}{{num : Num A}} (n : ℕ) → ExprN A n → Nest A n → A
semantics zero x tt = x
semantics {A} (suc n) e (t , es) rewrite numEquiv A n
    = let ins = toExprNumN n
      in semantics n (semantics1 {{ins}} e t) es
-}

semantics-aux : ∀ {A : Set} {n} → {w : Set} → w → w ≡ Expr (ExprN A n) → Expr (ExprN A n)
semantics-aux e refl = e

semantics : ∀ {A : Set}{{num : Num A}} (n : ℕ) → ExprN A n → Nest A n → A
semantics zero x tt = x
semantics {A} (suc n) e (t , es)
    = let ins = toExprNumN n
      in semantics n (semantics1 {{ins}} (semantics-aux {A} {n} e (numEquiv A n)) t) es

nestToNestRange : ∀ {A : Set} → {m : ℕ} → Nest A m → NestRange A m m
nestToNestRange {m = zero} n = tt
nestToNestRange {m = suc m} (proj₁ , proj₂)
    = proj₁ , (nestToNestRange proj₂)

nest-rev : ∀ {A : Set} (m n o : ℕ) → Nest A o
    → m + n ≡ o → NestRange A o m × Nest A n
nest-rev m zero o exp p rewrite zero-red {m} | p = nestToNestRange exp , tt
nest-rev zero (suc n) zero exp ()
nest-rev {A} zero (suc n) (suc o) (proj₁ , proj₂) p
   rewrite suc-≡-elim n o p = tt , proj₁ , proj₂
nest-rev (suc m) (suc n) zero exp ()
nest-rev (suc m) (suc n) (suc .(m + suc n)) (proj₁ , p) refl
   rewrite a+suc-b==suc-a+b m n
   = let a , b = nest-rev m (suc n) (suc (m + n)) p (a+suc-b==suc-a+b m n)
     in (proj₁ , a) , b

record Addr : Set where
  constructor [[_]]
  field
    addr : ℕ

data TAC (A : Set) : Set where
  ConstI : Addr -> A -> TAC A
  AddI : Addr -> Addr -> Addr -> TAC A
  SubI : Addr -> Addr -> Addr -> TAC A
  MulI : Addr -> Addr -> Addr -> TAC A

Ins : Set -> Set
Ins A = List (TAC A)



record SSA (A : Set) (B : Set) : Set where
  no-eta-equality
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

compile : ∀ {A : Set} (n : ℕ) → Vec Addr n
   → ExprN A n → SSA A (Addr × Ins A)
compile zero addr exp = compile0 exp
compile {A} (suc n) (x ∷ addr) exp
  = foldExpr (pass x) (compile n addr) (subst id (numEquiv A n) exp)

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

runSSA : ∀ {A : Set} {{_ : Num A}} → SSA A (Addr × Ins A) → Addr → Heap A → A
runSSA (ssa ssa1) addr h
  = let r , _ = ssa1 addr
        addr , ins = r
    in getHeap addr (runIns h ins) 

-- splitEnv' : ∀ {A : Set} (i n : ℕ) → Nest A n → Nest A (suc i)


splitEnv : ∀ {A : Set} (i n : ℕ) → i ≤ n → Nest A n → Nest A i
splitEnv zero n p e = tt
splitEnv (suc i) zero () e
splitEnv (suc i) (suc n) p e with i ≟ n
splitEnv {A} (suc i) (suc n) p₁ e | yes p = subst (λ x → ExprN A x × Nest A x) (sym p) e
splitEnv (suc i) (suc n) (s≤s p) (e₁ , e₂) | no ¬p = splitEnv (suc i) n (neq-le i n p ¬p) e₂

_!_ : ∀ {l} {A : Set l} {n : ℕ} → Vec A n → Fin n → A
(x ∷ v) ! zero = x
(x ∷ v) ! suc i = v ! i


comp-aux : ∀ {A : Set} (n : ℕ) (exp : ExprN (Expr A) n) → subst id (sym (numEquiv A n)) (subst id (numEquiv A n) exp) ≡ exp
comp-aux {A} n exp rewrite numEquiv A n = refl

comp-sem' : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
  → (exp : Expr (ExprN A n))
  → (env : Nest A (suc n))
  → (env₀ : Vec Addr (suc n))
  → (h : Heap A)
  → (n₀ : ℕ)
  → (n₀ ≥ (suc n))
  → (∀ (i : ℕ) → (p : i < suc n) → let eᵢ , envᵢ = splitEnv (suc i) (suc n) p env
                                   in getHeap [[ i ]] h ≡ semantics i eᵢ envᵢ ×
                                      semantics i eᵢ envᵢ ≡ getHeap (env₀ ! fromℕ≤ p) h)
  → semantics (suc n) (subst id (sym (numEquiv A n)) exp) env ≡
    runSSA (compile (suc n) env₀ (subst id (sym (numEquiv A n)) exp)) [[ n₀ ]] h
comp-sem' {A} zero Ind (proj₃ , tt) (x₁ ∷ []) h n₀ n₀≥suc-n cons
    with cons 0 (s≤s z≤n)
... | cons₁ , cons₂ = cons₂
comp-sem' {A} zero (Lit x₁) env env₀ h n₀ n₀≥suc-n cons = {!!}
comp-sem' {A} zero (Add exp exp₁) env env₀ h n₀ n₀≥suc-n cons = {!!}
comp-sem' {A} zero (Sub exp exp₁) env env₀ h n₀ n₀≥suc-n cons = {!!}
comp-sem' {A} zero (Mul exp exp₁) env env₀ h n₀ n₀≥suc-n cons = {!!}
comp-sem' {A} (suc n) exp env env₀ h n₀ n₀≥suc-n cons = {!!}


comp-sem : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
  → (exp : ExprN A n)
  → (env : Nest A n)
  → (env₀ : Vec Addr n)
  → (h : Heap A)
  → (n₀ : ℕ)
  → (n₀ ≥ n)
  → (∀ (i : ℕ) → (p : i < n) → let eᵢ , envᵢ = splitEnv (suc i) n p env
                               in getHeap [[ i ]] h ≡ semantics i eᵢ envᵢ ×
                                  semantics i eᵢ envᵢ ≡ getHeap (env₀ ! fromℕ≤ p) h)
  → semantics n exp env ≡ runSSA (compile n env₀ exp) [[ n₀ ]] h
comp-sem zero exp env env₀ h n₀ n₀p cons rewrite get-put [[ n₀ ]] exp h = refl
comp-sem {A} (suc n) exp env env₀ h n₀ n₀p cons
   = subst (λ x → semantics (suc n) x env ≡
             runSSA (compile (suc n) env₀ x) [[ n₀ ]] h)
           (comp-aux n exp)
           (comp-sem' n (subst id (numEquiv A n) exp) env env₀ h n₀ n₀p cons)

{-

comp-sem' : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
   → (exp : Expr (ExprN A n))
   → (env : Nest A (suc n))
   → (h : Heap A)
   → semantics (suc n) (subst id (sym (numEquiv A n)) exp) env ≡
     runSSA (compAll (suc n) env (subst id (sym (numEquiv A n)) exp)) h
comp-sem' {A} zero Ind env h = {!!}
comp-sem' {A} zero (Lit x₁) env h = {!!}
comp-sem' {A} zero (Add exp exp₁) env h = {!!}
comp-sem' {A} zero (Sub exp exp₁) env h = {!!}
comp-sem' {A} zero (Mul exp exp₁) env h = {!!}
comp-sem' {A} (suc n) exp env h = {!!}




comp-sem : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
   → (exp : ExprN A n)
   → (env : Nest A n)
   → (h : Heap A)
   → semantics n exp env ≡ runSSA (compAll n env exp) h
comp-sem zero exp env h = baseCase env exp h
comp-sem {A} (suc n) exp env h = subst (λ x -> semantics (suc n) x env ≡ runSSA (compAll (suc n) env x) h)
                                          (comp-aux n exp) (comp-sem' n (subst id (numEquiv A n) exp) env h)
-}
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
rotaExprN (suc (suc (suc n))) =
   fmapN {_} {1} (suc n) rotaExpr2 ∘ rotaExprN {{toExprNumN 1}} (suc (suc n))



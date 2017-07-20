open import Data.Unit using (⊤; tt)
open import Data.Nat hiding (_⊔_)
open import Data.List
open import Data.Product
open import Data.Vec hiding (_>>=_; _++_)
open import Num
open import NatProperties
open import Data.Nat.Properties.Simple
open import Level hiding (zero; suc)
open import Function
open import Relation.Binary.PropositionalEquality

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

-- NExprN : ∀ {l m} (A : Set l) (B : Set m) (n : ℕ) -> Set (l ⊔ m)
-- NExprN A B zero = ExprN A zero -> B
-- NExprN A B (suc n) = ExprN A (suc n) -> NExprN A B n
--
-- NExprN' : ∀ {l} (A : Set l) (m : ℕ) (n : ℕ) -> Set l
-- NExprN' A zero n = ExprN A n -> ExprN A n
-- NExprN' A (suc m) n = ExprN A n -> NExprN' A m n

Nest : Set -> ℕ -> Set
Nest A zero = ⊤
Nest A (suc n) = ExprN A n × Nest A n

-- Nest' : Set -> ℕ -> Set
-- Nest' A zero = A
-- Nest' A (suc n) = A × Nest' A n


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


semantics : ∀ {A : Set}{{num : Num A}} (n : ℕ) → ExprN A n → Nest A n → A
semantics zero x tt = x
semantics {A} (suc n) e (t , es) rewrite numEquiv A n
    = let ins = toExprNumN n
      in semantics n (semantics1 {{ins}} e t) es

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




getvar : ∀ {A : Set} → SSA A Addr
getvar = ssa (λ args → let [[ n ]] = args
                       in [[ n ]] , [[ suc n ]])
{-
putins : ∀ {A : Set} → TAC A → SSA A ⊤
putins i = ssa (λ args → let [[ n ]] , is = args
                         in tt , [[ n ]] , i ∷ is)
-}
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
  rewrite numEquiv A n
  = foldExpr (pass x) (compile n addr) exp


{-
 {-# NON_TERMINATING # -}
-- semantics : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> NExprN A (A -> A) n
-- semantics {{num}} zero = foldExpr {{toFuncNum num}} id const
-- semantics {{num}} (suc zero) e = semantics zero ∘ semantics {{toExprNum num}} zero e
-- semantics {A} {{num}} (suc (suc n)) e
--    = (semantics {{num}} (suc n) ∘
--           semantics {{toExprNumN {_} {suc n} {{num}}}}
--                zero (subst id (numEquiv n) e))

-}

-- {-# NON_TERMINATING #-}
-- semantics : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> Nest A n -> A -> A
-- semantics {{num}} zero = foldExpr {{toFuncNum num}} id const
-- semantics {{num}} (suc zero) (proj₁ , proj₂) = semantics zero (semantics {{toExprNum num}} zero proj₁ proj₂)
-- semantics {{num}} (suc (suc n)) (proj₁ , proj₂ , proj₃) =
--   semantics (suc n)
--     (semantics {{toExprNumN {_} {suc n} {{num}}}} zero
--                   (subst id (numEquiv n) proj₁) proj₂ , proj₃)

-- toProdFunc : ∀ {A : Set}{n : ℕ} -> NExprN A (A -> A) n -> Nest A n -> A -> A
-- toProdFunc {n = zero} x x₁ = x x₁
-- toProdFunc {n = suc n} x (proj₁ , proj₂) x₁ = toProdFunc (x proj₁) proj₂ x₁


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


-- {-# NON_TERMINATING #-}
-- rotrExpr : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> ExprN A n -> ExprN A n
-- rotrExpr zero x = x
-- rotrExpr {{num}} (suc zero) = foldExpr {{toExprNumN {_} {1} {{num}}}} (Lit Ind)
--                                           (foldExpr {{toExprNumN {_} {1} {{num}}}}
--                                               Ind (Lit ∘ Lit))
-- rotrExpr {A} {{num}} (suc (suc n)) x
--    = (fmapN {_} {1} (suc n) (rotrExpr {A} (suc zero))) (rotrExpr {{toExprNum num}} (suc n) x)

-- {-# NON_TERMINATING #-}
-- rotlExpr : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> ExprN A n -> ExprN A n
-- rotlExpr zero x = x
-- rotlExpr {{num}} (suc zero) = foldExpr {{toExprNumN {_} {1} {{num}}}} (Lit Ind)
--                                           (foldExpr {{toExprNumN {_} {1} {{num}}}}
--
--                                               Ind (Lit ∘ Lit))
-- rotlExpr {A} {{num}} (suc (suc n)) x
--    = (fmapN {_} {1} (suc n) (rotrExpr {A} (suc zero))) (rotrExpr {{toExprNum num}} (suc n) x)

{- SCM
{-# NON_TERMINATING #-}
sub : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> ExprN A n -> ExprN A n -> ExprN A n
sub zero Ind e' = e'
sub zero (Lit x) e' = Lit x
sub zero (Add e e₁) e' = Add (sub zero e e') (sub zero e₁ e')
sub zero (Sub e e₁) e' = Sub (sub zero e e') (sub zero e₁ e')
sub zero (Mul e e₁) e' = Mul (sub zero e e') (sub zero e₁ e')
sub {A} (suc n) e e' rewrite numEquiv {A} n
    with e
... | Ind       = e'
... | Lit x     = Lit x
... | Add e₁ e₂ = Add (subst id (numEquiv {A} n) (sub (suc n) (subst id (sym (numEquiv {A} n)) e₁) (subst id (sym (numEquiv {A} n)) e')))
                      (subst id (numEquiv {A} n) (sub (suc n) (subst id (sym (numEquiv {A} n)) e₂) (subst id (sym (numEquiv {A} n)) e')))
... | Sub e₁ e₂ = Sub (subst id (numEquiv {A} n) (sub (suc n) (subst id (sym (numEquiv {A} n)) e₁) (subst id (sym (numEquiv {A} n)) e')))
                      (subst id (numEquiv {A} n) (sub (suc n) (subst id (sym (numEquiv {A} n)) e₂) (subst id (sym (numEquiv {A} n)) e')))
... | Mul e₁ e₂ = Mul (subst id (numEquiv {A} n) (sub (suc n) (subst id (sym (numEquiv {A} n)) e₁) (subst id (sym (numEquiv {A} n)) e')))
                      (subst id (numEquiv {A} n) (sub (suc n) (subst id (sym (numEquiv {A} n)) e₂) (subst id (sym (numEquiv {A} n)) e')))

substitute' : ∀ {A : Set}{{num : Num A}} (n n' : ℕ) -> ExprN A n -> Nest' (ExprN A n) n' -> ExprN A n
substitute' n zero e e' = {! !}
substitute' n (suc n') e e' = {! !}



substitute : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> ExprN A n -> Nest' (ExprN A n) n -> ExprN A n
substitute zero e e' = {! !}
substitute (suc n) e e' = {! !}
-- rotrExpr 3 (Add Ind (Add (Lit Ind) (Lit (Lit Ind))))
SCM -}

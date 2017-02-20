open import Data.Nat hiding (_⊔_)
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
ExprN A zero = Expr A
ExprN A (suc n) = ExprN (Expr A) n

NExprN : ∀ {l m} (A : Set l) (B : Set m) (n : ℕ) -> Set (l ⊔ m)
NExprN A B zero = ExprN A zero -> B
NExprN A B (suc n) = ExprN A (suc n) -> NExprN A B n

NExprN' : ∀ {l o} (A : Set l) (B : Set o) (m : ℕ) (n : ℕ) -> Set (l ⊔ o)
NExprN' A B zero n = ExprN A n -> B
NExprN' A B (suc m) n = ExprN A n -> NExprN' A B m n


toFuncNum : ∀ {A : Set} (num : Num A) -> Num (A -> A)
toFuncNum record { +-id = +-id ; *-id = *-id ; _+_ = _+_ ; _-_ = _-_ ; _*_ = _*_ }
   = record { +-id = const +-id
            ; *-id = const *-id
            ; _+_ = \f g x -> f x + g x
            ; _-_ = \f g x -> f x - g x
            ; _*_ = \f g x -> f x * g x
            }
toExprNum : ∀ {A : Set} (num : Num A) -> Num (Expr A)
toExprNum record { +-id = +-id ; *-id = *-id ; _+_ = _+_ ; _-_ = _-_ ; _*_ = _*_ }
   = record { +-id = Lit +-id
            ; *-id = Lit  *-id
            ; _+_ = \e1 e2 -> Add e1 e2
            ; _-_ = \e1 e2 -> Sub e1 e2
            ; _*_ = \e1 e2 -> Mul e1 e2
            }

fmap : ∀ {A B : Set} -> (A -> B) -> Expr A -> Expr B
fmap f Ind = Ind
fmap f (Lit x) = Lit (f x)
fmap f (Add e e₁) = Add (fmap f e) (fmap f e₁)
fmap f (Sub e e₁) = Sub (fmap f e) (fmap f e₁)
fmap f (Mul e e₁) = Mul (fmap f e) (fmap f e₁)

numEquiv : ∀ {A : Set} (n : ℕ) -> ExprN (Expr A) n ≡ Expr (ExprN A n)
numEquiv zero = refl
numEquiv (suc n) = numEquiv n

exprLift : ∀ {l} {A : Set l} m n -> m ≤ n -> ExprN A m -> ExprN A n
exprLift _ zero z≤n exp = exp
exprLift zero (suc n) z≤n exp = exprLift 0 n z≤n (Lit exp)
exprLift (suc m) (suc n) (s≤s p) exp = exprLift m n p exp

compose : ∀ {A : Set} -> (n : ℕ) -> (A -> A) -> (A -> A)
compose zero f = f
compose (suc n) f = f ∘ compose n f

fmapN : ∀ {A : Set}{m} -> (n : ℕ) -> (ExprN A m -> ExprN A m) -> ExprN A (m + n) -> ExprN A (m + n)
fmapN {_} {m} zero f rewrite +-comm m zero = f
fmapN {A} {m} (suc n) f rewrite a+suc-b==suc-a+b m n
   = fmapN {_} {suc m} n (subst (\x -> x -> x) (sym $ numEquiv m) (fmap f))


toExprNumN : ∀ {A : Set}{n}{{num : Num A}} -> Num (ExprN A n)
toExprNumN {n = zero} {{num}} = toExprNum num
toExprNumN {A} {n = suc n} {{num}} rewrite numEquiv {A} n = toExprNum (toExprNumN {_} {n})

{-# NON_TERMINATING #-}
semantics : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> NExprN A (A -> A) n
semantics {{num}} zero = foldExpr {{toFuncNum num}} id const
semantics {{num}} (suc zero) e = semantics zero ∘ semantics {{toExprNum num}} zero e
semantics {A} {{num}} (suc (suc n)) e
   = (semantics {{num}} (suc n) ∘
          semantics {{toExprNumN {_} {suc n} {{num}}}}
               zero (subst id (numEquiv n) e))

{-# NON_TERMINATING #-}   
rotrExpr : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> ExprN A n -> ExprN A n
rotrExpr zero x = x
rotrExpr {{num}} (suc zero) = foldExpr {{toExprNumN {_} {1} {{num}}}} (Lit Ind)
                                          (foldExpr {{toExprNumN {_} {1} {{num}}}}
                                              Ind (Lit ∘ Lit))
rotrExpr {A} {{num}} (suc (suc n)) x
   = (fmapN {_} {1} (suc n) (rotrExpr {A} 1)) (rotrExpr {{toExprNum num}} (suc n) x)

substitute' : ∀ {A : Set}{{num : Num A}} (m n : ℕ) -> NExprN' A (ExprN A n) m n
substitute' zero n = {!!}
substitute' (suc m) n = {!!}

substitute : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> NExprN' A (ExprN A n) (suc n) n
substitute {{num}} n = substitute' (suc n) n  -- semantics {{toExprNum num}} 0 (rotrExpr 1 (Lit e)) e'




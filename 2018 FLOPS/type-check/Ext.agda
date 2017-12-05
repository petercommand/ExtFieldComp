open import Data.Nat renaming (_+_ to _ℕ+_)
open import Data.Product hiding (map; ,_)
open import Data.List hiding (map)
open import Data.Vec hiding (_>>=_; _++_)
open import Function
open import Relation.Nullary
open import Data.Unit hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties.Simple

-- ≤ utility

≤-refl : ∀ {a} -> a ≤ a
≤-refl {zero} = z≤n
≤-refl {suc a} = s≤s (≤-refl {a})

≤′-suc : ∀ a b → a ≤′ b → suc a ≤′ suc b
≤′-suc a .a ≤′-refl = ≤′-refl
≤′-suc a .(suc _) (≤′-step p) = ≤′-step (≤′-suc a _ p)

≤→≤′ : ∀ a b → a ≤ b → a ≤′ b
≤→≤′ zero zero = λ x → ≤′-refl
≤→≤′ zero (suc b) z≤n = ≤′-step (≤→≤′ zero b z≤n)
≤→≤′ (suc a) zero ()
≤→≤′ (suc a) (suc b) (s≤s p) = ≤′-suc a b (≤→≤′ a b p)


≤-weakening : (a b c : ℕ) -> a ≤ b -> a ≤ b ℕ+ c
≤-weakening .0 zero zero z≤n = z≤n
≤-weakening .0 zero (suc c) z≤n = z≤n
≤-weakening .0 (suc b) c z≤n = z≤n
≤-weakening (suc m) (suc n) c (s≤s p) = s≤s (≤-weakening m n c p)

--

data Poly (A : Set) : Set where
  Ind : Poly A
  Lit : A → Poly A
  _:+_ : Poly A → Poly A → Poly A
  _:x_ : Poly A → Poly A → Poly A


infixl 30 _:x_
infixl 20 _:+_

ex1 : Poly ℕ
ex1 = (Lit 2 :x Ind :x Ind) :+ (Lit 3 :x Ind) :+ Lit 1


foldP : ∀ {A B : Set} → B → (A → B)
        → (B → B → B) × (B → B → B) → Poly A → B
foldP x f rng Ind = x
foldP x f rng (Lit y) = f y
foldP x f (_+_ , _×_) (e₁ :+ e₂) = foldP x f (_+_ , _×_) e₁ +
                                   foldP x f (_+_ , _×_) e₂
foldP x f (_+_ , _×_) (e₁ :x e₂) = foldP x f (_+_ , _×_) e₁ ×
                                   foldP x f (_+_ , _×_) e₂

Ring : Set → Set
Ring A = ((A → A → A) × (A → A → A)) × A × A × (A → A)

ring→ : ∀ {A B : Set} → Ring B → Ring (A → B)
ring→ ((_+_ , _×_) , 𝟎 , 𝟏 , neg) =
   ((λ f g x → f x + g x) , (λ f g x → f x × g x)) ,
   const 𝟎 , const 𝟏 , (_∘_ neg)

-- ev : ∀ {A} → Ring A → (B → B → B) × (B → B → B)
-- ev (_+_ , _×_ , 𝟎 , 𝟏 , neg) = (_+_ , _×_ )


sem₁ : ∀ {A} → Ring A → Poly A → A → A
sem₁ rng = foldP id const (proj₁ (ring→ rng))


e : Poly (Poly ℕ)
e = (Lit (Lit 3) :x Ind :x Lit (Ind :+ Lit 4)) :+ Lit Ind :+ Ind


ringP : ∀ {A} → Ring A → Ring (Poly A)
ringP (_ , 𝟎 , 𝟏 , neg) =
  (_:+_ , _:x_) , Lit 𝟎 , Lit 𝟏 , _:x_ (Lit (neg 𝟏))

-- evaluating - sem₁ ringP e (Ind :+ Lit 1) - yields

e' : Poly ℕ
e' = Lit 3 :x (Ind :+ Lit 1) :x (Ind :+ Lit 4) :+ Ind :+ (Ind :+ Lit 1)

-- e'ₑ : sem₁ (ringP) e (Ind :+ Lit 1) ≡ e'
-- e'ₑ = refl

sem₂ : ∀ {A} → Ring A → Poly (Poly A) → Poly A → A → A
sem₂ r e₂ e₁ x = sem₁ r (sem₁ (ringP r) e₂ e₁) x

litDist : ∀ {A} → Poly (Poly A) → Poly (Poly A)
litDist = foldP Ind (foldP (Lit Ind) (Lit ∘ Lit) (_:+_ , _:x_)) (_:+_ , _:x_)

PolyN : Set → ℕ → Set
PolyN A zero = A
PolyN A (suc n) = Poly (PolyN A n)

DChain : Set → ℕ → Set
DChain A zero = ⊤
DChain A (suc n) = PolyN A n × DChain A n


--

ringP* : ∀ {A} → Ring A → ∀ n → Ring (PolyN A n)
ringP* r zero    = r
ringP* r (suc n) = ringP (ringP* r n)

sem : ∀ {A} → Ring A → (n : ℕ) → PolyN A n → DChain A n → A
sem r zero x tt = x
sem r (suc n) e (t , es) = sem r n (sem₁ (ringP* r n) e t) es

rotaPoly₂ : ∀ {A} → PolyN A 2 → PolyN A 2
rotaPoly₂ = foldP (Lit Ind) (foldP Ind (Lit ∘ Lit) (_:+_ , _:x_)) (_:+_ , _:x_)

fmap : ∀ {A B} → (A → B) → Poly A → Poly B
fmap f Ind = Ind
fmap f (Lit x) = Lit (f x)
fmap f (a :+ a₁) = fmap f a :+ fmap f a₁
fmap f (a :x a₁) = fmap f a :x fmap f a₁

rotaPoly₃ : ∀ {A} → PolyN A 3 → PolyN A 3
rotaPoly₃ = fmap rotaPoly₂ ∘ rotaPoly₂

rotaPoly₄ : ∀ {A} → PolyN A 4 → PolyN A 4
rotaPoly₄ = fmap (fmap rotaPoly₂) ∘ rotaPoly₃

--

a+suc-b≡suc-a+b : (a b : ℕ) → a ℕ+ (suc b) ≡ (suc (a ℕ+ b))
a+suc-b≡suc-a+b zero zero = refl
a+suc-b≡suc-a+b (suc x) zero = cong suc (a+suc-b≡suc-a+b x zero)
a+suc-b≡suc-a+b zero (suc y) = refl
a+suc-b≡suc-a+b (suc x) (suc y) = cong suc (a+suc-b≡suc-a+b x (suc y))

fmapN : ∀ {A : Set}{m} -> (n : ℕ) -> (PolyN A m -> PolyN A m) -> PolyN A (m ℕ+ n) -> PolyN A (m ℕ+ n)
fmapN {_} {m} zero f rewrite +-comm m zero = f
fmapN {A} {m} (suc n) f rewrite a+suc-b≡suc-a+b m n
   = fmapN {_} {suc m} n (fmap f)

polyEquiv : ∀ (A : Set) (n : ℕ) -> PolyN (Poly A) n ≡ Poly (PolyN A n)
polyEquiv _ zero = refl
polyEquiv _ (suc n) = cong Poly (polyEquiv _ n)

PolyN-comb : ∀ {A : Set} m n → PolyN (PolyN A m) n ≡ PolyN A (m ℕ+ n)
PolyN-comb zero n = refl
PolyN-comb {A} (suc m) n rewrite polyEquiv (PolyN A m) n = cong Poly (PolyN-comb m n)

liftPoly : ∀ {A : Set} {m n : ℕ} → m ≤′ n → PolyN A m → PolyN A n
liftPoly {m = m} {.m} ≤′-refl e = e
liftPoly {m = m} {.(suc _)} (≤′-step p) e = Lit (liftPoly p e)

liftVal : ∀ {A : Set} n → A → PolyN A n
liftVal zero x = x
liftVal (suc n) x = Lit (liftVal n x)

toDChain : ∀ {A : Set} n → Vec A n → DChain A n
toDChain zero [] = tt
toDChain (suc n) (x ∷ xs) = liftVal n x , toDChain n xs


--
rotaPoly : ∀ {A} (n : ℕ) → PolyN A n → PolyN A n
rotaPoly zero = id
rotaPoly (suc zero) = id
rotaPoly (suc (suc zero)) = rotaPoly₂
rotaPoly (suc (suc (suc n))) = subst (λ x → Poly (Poly x) → Poly (Poly x))
   (polyEquiv _ n)
   (fmapN {_} {1} (suc n) rotaPoly₂ ∘ rotaPoly (suc (suc n)))

rotaOuter : ∀ {A : Set} (n m : ℕ) → PolyN A n → PolyN A n
rotaOuter n zero = id
rotaOuter n (suc m) = rotaOuter n m ∘ rotaPoly n

substitute₁ : ∀ {A} → Ring A → Poly A → Poly A → Poly A
substitute₁ r e e' = sem₁ (ringP r) (rotaPoly₂ (Lit e)) e'

substitute₂ : ∀ {A} → Ring A → PolyN A 2 → PolyN A 2 → PolyN A 2 → PolyN A 2
substitute₂ r e e' e'' = sem₂ (ringP (ringP r)) (rotaPoly₄ ∘ rotaPoly₄ $ Lit (Lit e)) (Lit e') e''

substitute : ∀ {A} n → Ring A → PolyN A n → Vec (PolyN A n) n → PolyN A n
substitute {A} n r e e'
  = sem (ringP* r n) n
        (subst id (sym (PolyN-comb {A} n n))
          (rotaOuter (n ℕ+ n) n
             (liftPoly {_} {n} {n ℕ+ n} ≤-prf e)))
        (toDChain n e')
        where
         ≤-prf : n ≤′ n ℕ+ n
         ≤-prf = ≤→≤′ n (n ℕ+ n) (≤-weakening n n n ≤-refl)

genInd : ∀ {A} n → Vec (PolyN A n) n
genInd zero = []
genInd (suc zero) = Ind ∷ []
genInd (suc (suc n)) = Ind ∷ map Lit (genInd (suc n))

RingVec : ℕ → Set₁
RingVec n = ∀ {A} → Ring A → Ring (Vec A n)

-- we don't have minus here, is this a problem?

-- rComplex : RingVec 2
-- rComplex (+ , x) = +c , xc
--    where
--      _+c_ : ?
--      (x₁ , y₁) +c (x₂ , y₂) = x₁ + x₂ , y₁ + y₂
--
--      _xc_ : ?
--      (x₁ , y₁) xc (x₂ , y₂) = x₁ x x₂ - y₁ x y₂ , x₁ + y₂ + x₂ × y₁

postulate rComplex : RingVec 2

-- expand : ∀ {A} n → Ring A → RingVec n → Poly (Vec A n) → Vec (PolyN A n) n
-- expand n ringA ringVec =
--   foldP (genInd n) (map (liftVal n)) (ringVec (ringP* ringA {n}))

expand : ∀ {A} n → Ring (Vec (PolyN A n) n) → Poly (Vec A n) → Vec (PolyN A n) n
expand n rv = foldP (genInd n) (map (liftVal n)) (proj₁ rv)

expandComplex : ∀ {A} → Ring A → Poly (Vec A 2) → Vec (PolyN A 2) 2
expandComplex r = expand 2 (rComplex (ringP (ringP r)))

expandCorrect : ∀ {A} n → Ring A → RingVec n → Poly (Vec A n) → Vec A n → Set
expandCorrect n r ringVec e xs =
  sem₁ (ringVec r) e xs ≡
    map (λ e → sem r n e (toDChain _ xs))
      (expand n (ringVec (ringP* r n)) e)

postulate
  Word : Set

Addr = ℕ

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


data TAC : Set where
  Const : Addr → Word → TAC
  Add : Addr → Addr → Addr → TAC
  Mul : Addr → Addr → Addr → TAC

Ins : Set
Ins = List TAC

compile₀ : Word → SSA (Addr × Ins)
compile₀ v = alloc >>= λ addr →
             return (addr , Const addr v ∷ [])


biOp : (Addr → Addr → Addr → TAC)
    → SSA (Addr × Ins) → SSA (Addr × Ins) → SSA (Addr × Ins)
biOp op m1 m2 = m1 >>= λ x →
                m2 >>= λ y →
                alloc >>= λ dest →
                let (addr1 , ins1) = x
                    (addr2 , ins2) = y
                in return (dest , ins1 ++ ins2 ++ (op dest addr1 addr2 ∷ []))

-- ringSSA : Ring (SSA (Addr × Ins))
-- ringSSA = biOp Add , biOp Mul

compile : ∀ n → Vec Addr n → PolyN Word n → SSA (Addr × Ins)
compile zero addr = compile₀
compile (suc n) (x ∷ addr)
  = foldP (return (x , [])) (compile n addr) (biOp Add , biOp Mul)

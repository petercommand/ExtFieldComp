open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
import Data.Nat.Properties.Simple as NS

max : ℕ -> ℕ -> ℕ
max zero b = b
max (suc a) zero = suc a
max (suc a) (suc b) = suc (max a b)

suc-<-elim : (a b : ℕ) -> (suc a ≤ suc b) -> (a ≤ b)
suc-<-elim zero zero = λ x → z≤n
suc-<-elim zero (suc b) = λ x → z≤n
suc-<-elim (suc a) zero (s≤s ())
suc-<-elim (suc a) (suc b) (s≤s p) = p

suc-≡-elim : (a b : ℕ) -> (suc a ≡ suc b) -> a ≡ b
suc-≡-elim a .a refl = refl

suc-≤-elim' : (a b : ℕ) -> (suc a ≤ b) -> a ≤ b
suc-≤-elim' zero _ (s≤s p) = z≤n
suc-≤-elim' (suc a) _ (s≤s p) = s≤s (suc-≤-elim' a _ p)

suc-<-intro : {a b : ℕ} -> (a ≤ b) -> (suc a ≤ suc b)
suc-<-intro = s≤s

--add preserve <
zero-red : {a : ℕ} -> a + zero ≡ a
zero-red {zero} = refl
zero-red {suc a} = cong (\x -> suc x) (zero-red {a})

a+suc-b==suc-a+b : (a b : ℕ) -> a + (suc b) ≡ (suc (a + b))
a+suc-b==suc-a+b zero zero = refl
a+suc-b==suc-a+b (suc x) zero = cong suc (a+suc-b==suc-a+b x zero)
a+suc-b==suc-a+b zero (suc y) = refl
a+suc-b==suc-a+b (suc x) (suc y) = cong suc (a+suc-b==suc-a+b x (suc y))

+suc-1 : ∀ (a : ℕ) -> suc a ≡ a + 1
+suc-1 zero = refl
+suc-1 (suc a) = cong suc (+suc-1 a)

a-suc-b==b-suc-a : (a b : ℕ) -> (a + suc b) ≡ (b + suc a)
a-suc-b==b-suc-a x zero = trans (a+suc-b==suc-a+b x zero) (cong suc zero-red)
a-suc-b==b-suc-a zero (suc y) = trans (a+suc-b==suc-a+b (suc zero) y) (cong suc (sym (trans (a+suc-b==suc-a+b y zero) (cong suc zero-red))))
a-suc-b==b-suc-a (suc x) (suc y) = trans (cong suc (a-suc-b==b-suc-a x (suc y))) (cong suc (sym (a+suc-b==suc-a+b y (suc x))))


+<weakening : (a b c : ℕ) -> a < b -> a < b + c
+<weakening zero zero zero ()
+<weakening zero zero (suc c) p = s≤s z≤n
+<weakening zero (suc b) zero (s≤s z≤n) = s≤s z≤n
+<weakening zero (suc b) (suc c) (s≤s p) = s≤s z≤n
+<weakening (suc a) zero c ()
+<weakening (suc a) (suc b) zero (s≤s p) rewrite zero-red {suc b} = s≤s p
+<weakening (suc a) (suc b) (suc c) p rewrite sym (a+suc-b==suc-a+b b (suc c))
                                            | trans (a-suc-b==b-suc-a b (suc c)) (NS.+-comm (suc c) (suc b))
                                            = suc-<-intro (+<weakening a b (suc c) (suc-<-elim (suc a) b p))


≤-weakening : (a b c : ℕ) -> a ≤ b -> a ≤ b + c
≤-weakening .0 zero zero z≤n = z≤n
≤-weakening .0 zero (suc c) z≤n = z≤n
≤-weakening .0 (suc b) c z≤n = z≤n
≤-weakening (suc m) (suc n) c (s≤s p) = s≤s (≤-weakening m n c p)

≤weak : {a b : ℕ} -> suc a ≤ b -> a ≤ b
≤weak {zero} {_} (s≤s p) = z≤n
≤weak {suc a} {suc b} (s≤s p) = s≤s (≤weak {a} {b} p)

≤-suc : (a b : ℕ) -> a ≤ b -> a ≤ suc b
≤-suc zero b p = z≤n
≤-suc (suc a) b p = s≤s (≤weak p)


lem : (b c d : ℕ) -> (_ : 0 ≤ b) -> (_ : suc c ≤ d) -> suc c ≤ b + d
lem zero zero _ z≤n (s≤s p3) = s≤s z≤n
lem zero (suc c) (suc d) z≤n (s≤s p3) = s≤s p3
lem (suc b) zero (suc d) z≤n (s≤s p3) = s≤s z≤n
lem (suc b) (suc c) (suc d) z≤n (s≤s p3) = s≤s (lem b c (suc d) z≤n (s≤s (≤weak {c} {d} p3)))



+preserve< : (a b c d : ℕ) -> a < b -> c < d -> a + c < b + d
+preserve< zero _ zero _ (s≤s p1) (s≤s p2) = s≤s z≤n
+preserve< zero (suc b) (suc c) (suc d) (s≤s p1) (s≤s p2) rewrite a+suc-b==suc-a+b b d = s≤s (s≤s (≤weak (lem b c d p1 p2)))
+preserve< (suc a) (suc b) zero (suc d) (s≤s p1) (s≤s p2) rewrite a+suc-b==suc-a+b b d
                                                                | zero-red {a}
                                                                | NS.+-comm b d = s≤s (s≤s (≤weak (lem d a b p2 p1)))
+preserve< (suc a) (suc b) (suc c) (suc d) (s≤s p1) (s≤s p2) rewrite a+suc-b==suc-a+b b d
                                                                   | a+suc-b==suc-a+b a c = s≤s (s≤s (+preserve< a b c d p1 p2))

≤-refl : ∀ {a} -> a ≤ a
≤-refl {zero} = z≤n
≤-refl {suc a} = s≤s (≤-refl {a})

≤-trans : ∀ {a b c} -> a ≤ b -> b ≤ c -> a ≤ c
≤-trans z≤n z≤n = z≤n
≤-trans z≤n (s≤s p2) = z≤n
≤-trans (s≤s p1) (s≤s p2) = s≤s (≤-trans p1 p2)

a<c->¬a≡c : ∀ (a c : ℕ) -> a < c -> ¬ (a ≡ c)
a<c->¬a≡c .0 (suc c) (s≤s z≤n) a≡c = aux a≡c
  where
      aux : ∀ {a} -> ¬ (0 ≡ suc a)
      aux ()
a<c->¬a≡c _ (suc _) (s≤s (s≤s a≤c₁)) a≡c = a<c->¬a≡c _ _ (suc-<-intro a≤c₁)
                                          (cong (λ { (suc n) -> n
                                                   ; zero -> zero }) a≡c)

a<c->¬c≡a : ∀ (a c : ℕ) -> a < c -> ¬ (c ≡ a)
a<c->¬c≡a a c a<c = λ x → a<c->¬a≡c a c a<c (sym x)

a≤suc-a : ∀ (a : ℕ) -> a ≤ suc a
a≤suc-a zero = z≤n
a≤suc-a (suc a) = s≤s (a≤suc-a a)

data Acc (n : ℕ) : Set where
  acc : (∀ m → m < n → Acc m) → Acc n

<-wf : ∀ n -> Acc n
<-wf n = acc (go n)
  where
  go : ∀ n m -> m < n -> Acc m
  go (suc n) zero (s≤s p) = acc (λ m ())
  go (suc n) (suc m) (s≤s p) = acc (λ m1 p1 -> go n m1 (≤-trans p1 p))



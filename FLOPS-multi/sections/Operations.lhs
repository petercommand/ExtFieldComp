 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Operations on Polynomials}
\label{sec:operations}

Having defined a representation for multivariate polynomials, we ought to
demonstrate that this representation is feasible --- that we can define most of the operations we want.

\subsection{Rotation}

The first operation we consider swaps the two outermost indeterminates
of an |Poly2 A|, using |foldP|.
%
This implements the isomorphism between $R[X_1,\ldots,X_{m-1}][X_m]$
and $R[X_m,X_1,\ldots,X_{m-2}][X_{m-1}]$.
%
It is perhaps instructive comparing it with |litDist|.
\begin{spec}
rotaPoly2 : ∀ {A} → Poly2 A → Poly2 A
rotaPoly2 = foldP (Lit Ind) (foldP Ind (Lit ∘ Lit) ringP) ringP {-"~~."-}
\end{spec}
In |rotaPoly2|, the outermost |Ind| is replaced by |Lit Ind|. When
encountering |Lit e|, the inner |e| is lifted to |Poly2 A|. The |Ind| inside
|e| remains |Ind|, which becomes the outermost indeterminate after lifting.
Note that both |litDist| and |rotaPoly2| apply to |PolyN n A| for all |n ≥ 2|,
since |A| can be instantiated to a polynomial as well.

Consider |PolyN 3 A|, a polynomial with (at least) three indeterminates. To
``rotate'' the three indeterminates, that is, turn |Lit Ind| to |Ind|, |Lit (Lit Ind)| to |Lit Ind|, and |Ind| to |LitN 3 Ind|, we could do:
\begin{spec}
  rotaPoly3 = fmap rotaPoly2 ∘ rotaPoly2 {-"~~,"-}
\end{spec}
where |fmap| is the usual ``map'' function:
\begin{spec}
  fmap : ∀ {A B} -> (A -> B) -> Poly A -> Poly B {-"~~."-}
\end{spec}
The first |rotaPoly2| swaps the two outer indeterminates, while |fmap rotaPoly2|
swaps the inner two. To rotate the outermost four indeterminates of an |PolyN 4 A|, we may define:
\begin{spec}
rotaPoly4 = fmap (fmap rotaPoly2) . rotaPoly3 {-"~~."-}
\end{spec}
In general, the following function rotates the first |n| indeterminates of
the given polynomial:%
\begin{spec}
rotaPolyN : ∀ {A} (n : ℕ) → PolyNn A → PolyNn A
rotaPolyN zero                 = id
rotaPolyN (suc zero)           = id
rotaPolyN (suc (suc zero))     = rotaPoly2
rotaPolyN (suc (suc (suc n)))  = (fmapN (suc n)) rotaPoly2 . rotaPolyN  (suc (suc n)) {-"~~."-}
\end{spec}
Note that in the actual Agda code we need to convince Agda that
|PolyN n (Poly A)| is the same type as |Poly (PolyN n A)| and use |subst|
to coerce between the two types.
%
We omit those details for clarity.

Given |m| and |n|, |rotaOuter n m| compose |rotaPolyN n| with itself
|m| times. Therefore, the outermost |n| indeterminates are rotated |m| times.
%
It will be handy in the next section.
\begin{spec}
rotaOuter : ∀ {A} (n m : ℕ) → PolyNn A → PolyNn A
rotaOuter n zero e = e
rotaOuter n (suc m) e = rotaOuter n m (rotaPolyN n e) {-"~~."-}
\end{spec}

\subsection{Substitution}

%format substitute1 = "\Varid{substitute}_{1}"
%format substitute2 = "\Varid{substitute}_{2}"

Substitution is another operation one would expect. Given an expression |e|,
how do we substitute, for each occurrence of |Ind|, another expression |e'|,
using operations we have defined? Recalling that the type of
|sem1| can be instantiated to |PolyN 2 A → Poly A → Poly A|, we may
lift |e| to |PolyN 2 A| by wrapping it with |Lit|, do a |rotaPoly2| to
expose the |Ind| inside |e|, and use |sem1| to perform the
substitution:
\begin{spec}
substitute1 : ∀ {A} → Poly A → Poly A → Poly A
substitute1 e e' = sem1 ringP (rotaPoly2 (Lit e)) e' {-"~~."-}
\end{spec}
What about |e : Poly2 A|? We may lift it to an |PolyN 4 A|, perform two
|rotaPoly4| to expose its two indeterminates, before using |sem2|:
\begin{spec}
substitute2 :: ∀ {A} → Poly2 A -> Poly2 A -> Poly2 A -> Poly2 A
substitute2 e e' e'' =
  sem2 ringP (rotaPoly4 . rotaPoly4 $ Lit (Lit e)) (Lit e') e'' {-"~~."-}
\end{spec}

We now consider the general case with substituting the |n| indeterminates in |e : PolyNn A| for |n| expressions, each of type |PolyN n A|. Let |Vec B n| be the type of vectors (lists of fixed lengths) of length |n|.
\todo{can be simplified.}
\begin{spec}
substitute : ∀ {A} n -> Ring A -> PolyNn A -> Vec (PolyNn A) n -> PolyNn A
substitute {A} n r e e'
   = sem (ringPS r {n}) n
        (subst id (sym (PolyN-comb {A} n n))
          (rotaOuter (n + n) n
             (liftPoly {_} {n} {n + n}
               (≤→≤′ n (n + n) (≤-weakening n n n ≤-refl)) e)))
        (Vec→DChain n e')
\end{spec}

\subsection{Expansion}

Expansion is an operation we will put specific emphasis on.
%
As we have seen in Section~\ref{sec:introduction}, this is especially
useful when implementing cryptosystems on microprocessors with no
native hardware support for arithmetic operations with polynomials or
integers of cryptographic sizes.
%
Let us use a very simple yet specific example for further exposition.
%
For example, the polynomial expression over complex numbers
$(3 + 2i) x^2 + (2 + i)x + 1$ can be represented by |Poly (Real ×
Real)|, whose semantics is a function |(Real × Real) -> (Real ×
Real)|.
%
Let $x$ be $x_1 + x_2 i$, the polynomial can be expanded as below:
\begin{align*}
  & (3 + 2i)(x_1 + x_2 i)^2 + (2 + i)(x_1 + x_2 i) + 1 \\
=~& (3 x^2_1 - 4 x_1 x_2 - 3 x^2_2) + (2 x^2_1 + 6 x_1 x_2 - 2 x^2_2) i +
  (2 x_1 - x_2) + (x_1 + 2 x_2) i + 1\\
=~& (3 x^2_1 + 2 x_1 - 4 x_1 x_2 - x_2 - 3 x^2_2 + 1) +
   (2 x^2_1 + x_1 + 6 x_1 x_2 + 2 x_2 - 2x^2_2) i \mbox{~~.}
\end{align*}
%format WordN = "\Varid{Word}^{\Varid{n}}"
That is, a univariate polynomial over pairs, |Poly (Real × Real)|, can
be expanded to |(Poly2 Real × Poly2 Real)|, a pair of bivariate
expressions.
%
The expansion depends on the definitions of addition and
multiplication of complex numbers.
%
It might turn out that |Real| is represented by a fixed length of
machine words, |Real = WordN|, and |Poly WordN| can be further
expanded to $|(PolyN n Word)|^\Varid{n}$, this time using arithmetic
operations defined for |Word|.
%
Now that each polynomial is defined over |Word|, whose arithmetic
operation has native support from the hardware, we may compile the
expressions, in ways discussed in the next section, into a sequence of
operations in a lower-level programming language such as the assembly
language.
%
We also note that the roles played by the indeterminates $x$ and $i$
are of fundamental difference: $x$ might just represent the input of
the computation modeled by the polynomial expression, which will be
substituted by some values at runtime, whereas $i$ intends to model
some internal (algebraic) structures and is never substituted
throughout the whole computation.
%

%
Currently, such conversion and compilation are typically done by hand.
%
We would like to define expansion in this section and compilation in
the next, as well as proving their correctness.
%
Furthermore, expansion and it proof of correctness should take the
arithmetic operation of its base type as parameters.
%

%format LitN1 = "\Varid{Lit}^{\Varid{n-1}}"
%format x1 = "\Varid{x}_1"
%format x2 = "\Varid{x}_2"
In general, a univariate polynomial of |n|-vectors, |Poly (Vec A n)|, can be
expanded to a |n|-vector of |n|-variate polynomial, |Vec (PolyN n A) n|. To
formally define expansion we need some helper functions. Firstly,
|genInd n| generates a vector |Ind ∷ Lit Ind ∷ ... LitN1 Ind ∷ []|. It corresponds
to expanding |x| to |(x1 , x2)|.
\begin{spec}
genInd : ∀ {A} n → Vec (PolyN n A) n
genInd zero           = []
genInd (suc zero)     = Ind ∷ []
genInd (suc (suc n))  = Ind ∷ (map Lit (genInd (suc n))) {-"~~."-}
\end{spec}
Secondly, |liftVal : ∀ {A} n → A → PolyNn A| lifts |A| to |PolyNn A| by |n| applications of |Lit|. The definition is routine. Finally, we define the type of operations that, given arithmetic operators for |A|, define arithmetic operators for vectors of |A|:
\begin{spec}
RingVec : ℕ -> Set1
RingVec n = ∀ {A} -> Ring A -> Ring (Vec A n) {-"~~."-}
\end{spec}
%format addC = "(\mathbin{+_c})"
%format `addC` = "\mathbin{+_c}"
%format mulC = "(\mathbin{\times_c})"
%format `mulC` = "\mathbin{\times_c}"

For example, |rComplex| lifts arithmetic operations on |A| to
that of complex numbers over |A|:
\begin{spec}
rComplex : RingVec 2
rComplex ((+),(×)) = (addC , mulC)
  where  [ x1, y1 ] `addC` [ x2, y2 ] = [ x1 + x2, y1 + y2 ]
         [ x1, y1 ] `mulC` [ x2, y2 ] = [ x1 × x2 - y1 × y2 ,  x1 × y2 + x2 × y1 ]{-"~~."-}
\end{spec}
% where  (x1 ∷ y1 ∷ []) `addC` (x2 ∷ y2 ∷ []) = (x1 + x2) ∷ (y1 + y2) ∷ []
%        (x1 ∷ y1 ∷ []) `mulC` (x2 ∷ y2 ∷ []) =
%          (x1 × x2 - y1 × y2) ∷ (x1 × y2 + x2 × y1) ∷ []{-"~~."-}
Expansion can now be defined by:
\begin{spec}
expand : ∀ {A n} → RingVec n → Poly (Vec A n) → Vec (PolyN n A) n
expand ringVec = foldP (genInd n) (map (liftVal n)) (ringVec ringP) {-"~~."-}
\end{spec}
For the |Ind| case, one indeterminant is expanded to |n| using |genInd|. For the
|Lit xs| case, |xs : Vec A n| can be lifted to |Vec (PolyN n A) n| by |map (liftVal n)|.
For addition and multiplication, we let |ringVec| decide how to combine vectors
of expressions, but specifying |((:+), (:×))| as atomic operations.

The readers may raise their doubts: we have not defined much, since all the real work is done in |ringVec ringP|. Indeed, the correctness of |expand| relies on |ringVec| being well-behaved, as we shall see soon.

\paragraph{Correctness.} Intuitively, |expand| is correct if the expanded
polynomial evaluates to the same value as the that of the original. To
formally state the property, we have to properly supply all the needed ingredients. Consider |e : Poly (Vec A n)| --- a polynomial whose coefficients are vectors of length |n|. Let |r : Ring A| define arithmetic operators for |A|, and let |ringVec : RingVec n| define how arithmetic operators for elements are lifted to vectors. We say that |expand| is correct if, for all |xs : Vec A n|:
\begin{equation}
\begin{split}
  &|sem1 (ringVec r) e xs =|\\
  &\quad  |map (\ e → sem r n e (toDChain xs)) (expand ringVec n e)| \mbox{~~.}
\end{split}
\label{eq:expand-correct}
\end{equation}
On the lefthand side, |e| is evaluated by |sem1|, using operators supplied by |ringVec r|. The value of the single indeterminant is |xs : Vec A n|, and the result also has type |Vec A n|. On the righthand side, |e| is expanded to |Vec (PolyN n A) n|. Internally, |expand| uses |ringVec ringP| to combine vectors of expressions. Each polynomial in the vector is evaluated individually by |sem r n|. The function |toDChain| converts a vector to a descending chain. The |n| elements in |xs| thus substitutes the |n| indeterminants of the expanded polynomial.

Interestingly, it turns out that |expand| is correct if |ringVec| is polymorphic --- that is, the way it computes vectors out of vectors depends only on the shape of its input, regardless of the type and the contents.
\begin{theorem} For all |n|, |e : Poly (Vec A n)|, |xs : Vec A n|,
|r : Ring A|, and |ringVec : RingVec|, property \eqref{eq:expand-correct} holds if |ringVec| is polymorphic.
\end{theorem}
\begin{proof}
Induction on |e|. For the base cases we need two lemmas:
\begin{itemize}
%\begin{lemma}\label{lma:sem-liftVal}
\item for all |n|, |x|, |es : DChain A n|, and |r : Ring A|,
we have |sem r n (liftVal n x) es = x|;
%\end{lemma}
%\begin{lemma} \label{lma:sem-genInd}
\item for all |n|, |xs : Vec A n|, and |r : Ring A|, we have\\
|map (\ e → sem r n e (toDChain xs)) (genInd n) = xs|.
%\end{lemma}
\end{itemize}
%format addP = "({+_\Conid{P}})"
%format `addP` = "\mathbin{+_\Conid{P}}"
%format addA = "({+_\Conid{A}})"
%format `addA` = "\mathbin{+_\Conid{A}}"
The inductive case where |e := e1 :+ e2| eventually comes down to proving
that (abbreviating |\ e → sem r n e (toDChainxs)| to |sem'|):
\begin{spec}
map sem' (expand ringVec n e1) `addA` map sem' (expand ringVec n e2) =
  map sem' (expand ringVec n e1 `addP` expand ringVec n e2)
\end{spec}
where |addA = fst (ringVec r)| perform addition on vectors of |A|'s, and |addP = fst (ringVec ringP)| on vectors of polynomials. But this is implied by the free theorem of |ringVec|. Specifically, |fst . ringVec| has type
\begin{spec}
  {A : Set}  -> (A -> A -> A) × (A -> A -> A)
             -> (Vec A n -> Vec A n -> Vec A n) {-"~~."-}
\end{spec}
The free theorem it induces is
%format add1 = "({+_1})"
%format `add1` = "\mathbin{+_1}"
%format add2 = "({+_2})"
%format `add2` = "\mathbin{+_2}"
%format addV1 = "({+_{\Conid{V}1}})"
%format `addV1` = "\mathbin{+_{\Conid{V}1}}"
%format addV2 = "({+_{\Conid{V}2}})"
%format `addV2` = "\mathbin{+_{\Conid{V}2}}"
%format mul1 = "({×_1})"
%format `mul1` = "\mathbin{×_1}"
%format mul2 = "({×_2})"
%format `mul2` = "\mathbin{×_2}"
\begin{spec}
∀ (X Y : Set) n ->
  ∀ (f : X -> Y)  (add1 : X -> X -> X) (mul1 : X -> X -> X)
                  (add2 : Y -> Y -> Y) (mul2 : Y -> Y -> Y) ->
  ∀ (xs ys : Vec X n) ->
    let  addV1 = fst (ringVec (add1 , mul1))
         addV2 = fst (ringVec (add2 , mul2))
    in map f (xs `addV1` ys) = map f xs `addV2` map f ys {-"~~,"-}
\end{spec}
which is exactly what we need. The case for |e := e1 :× e2| is similar.
\end{proof}

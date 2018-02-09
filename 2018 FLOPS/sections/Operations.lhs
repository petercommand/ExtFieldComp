%include agda.fmt
%include Formatting.fmt

\section{Operations on Polynomials}
\label{sec:operations}

Having defined a representation for multivariate polynomials, we ought to
demonstrate that this representation is feasible --- that we can define most of
the operations we want.
%
In fact, it turns that most of them can be defined either in terms of |foldP|
or by induction over the number of iterations |Poly| is applied.

\subsection{Rotation}
\label{sec:rotation}

The first operation swaps the two outermost indeterminates of a |Poly2 A|,
using |foldP|.
%
This function witnesses the isomorphism between $R[X_1,\ldots,X_{m-1}][X_m]$
and $R[X_m,X_1,\ldots,X_{m-2}][X_{m-1}]$.
%
It is instructive comparing it with |litDist|.
\begin{spec}
rotaPoly2 : ∀ {A} → Poly2 A → Poly2 A
rotaPoly2 = foldP (Lit Ind) (foldP Ind (Lit ∘ Lit) ((:+), (:×))) ((:+), (:×)) {-"~~."-}
\end{spec}
In |rotaPoly2|, the outermost |Ind| is replaced by |Lit Ind|. When
encountering |Lit e|, the inner |e| is lifted to |Poly2 A|. The |Ind| inside
|e| remains |Ind|, which becomes the outermost indeterminate after lifting.
Note that both |litDist| and |rotaPoly2| apply to |PolyN n A| for all |n ≥ 2|,
since |A| can be instantiated to a polynomial as well.

Consider |PolyN 3 A|, a polynomial with (at least) three indeterminates. To
``rotate'' the three indeterminates, that is, turn |LitN 2 Ind| to |Lit Ind|,
|Lit Ind| to |Ind|, and |Ind| to |LitN 2 Ind|, we can define:
\begin{spec}
  rotaPoly3 = fmap rotaPoly2 ∘ rotaPoly2 {-"~~,"-}
\end{spec}
where |fmap| is the usual ``functorial map'' function for |Poly|:
\begin{spec}
  fmap : ∀ {A B} -> (A -> B) -> Poly A -> Poly B {-"~~."-}
\end{spec}
The first |rotaPoly2| swaps the two outer indeterminates, while |fmap rotaPoly2|
swaps the inner two. To rotate the outermost four indeterminates of a |PolyN 4 A|, we may define:
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
Note that in the actual code we need to convince Agda that
|PolyN n (Poly A)| is the same type as |Poly (PolyN n A)| and use |subst|
to coerce between the two types.
%
We omit those details for clarity.

Given |m| and |n|, |rotaOuter n m| compose |rotaPolyN n| with itself
|m| times. Therefore, the outermost |n| indeterminates are rotated |m| times.
%
It will be handy in Section \ref{sec:substitution}.
\begin{spec}
rotaOuter : ∀ {A} (n m : ℕ) → PolyNn A → PolyNn A
rotaOuter n zero     = id
rotaOuter n (suc m)  = rotaOuter n m . rotaPolyN n e {-"~~."-}
\end{spec}

\subsection{Substitution}
\label{sec:substitution}

%format substitute1 = "\Varid{substitute}_{1}"
%format substitute2 = "\Varid{substitute}_{2}"

Substitution is another operation that one would expect.
%
Given an expression |e|, how do we substitute, for each occurrence of |Ind|, another expression |e'|, using operations we have defined?
%
Noticing that the type of |sem1| can be instantiated to |PolyN 2 A → Poly A → Poly A|, we may lift |e| to |PolyN 2 A| by wrapping it with |Lit|, do a |rotaPoly2| to swap the |Ind| in |e| to the outermost position, and use |sem1| to perform the substitution:
\begin{spec}
substitute1 : ∀ {A} → Ring A → Poly A → Poly A → Poly A
substitute1 r e e' = sem1 (ringP r) (rotaPoly2 (Lit e)) e' {-"~~."-}
\end{spec}
What about |e : Poly2 A|? We may lift it to |PolyN 4 A|, perform two
|rotaPoly4| to expose its two indeterminates, before using |sem2|:
\begin{spec}
substitute2 :: ∀ {A} → Ring A -> Poly2 A -> Poly2 A -> Poly2 A -> Poly2 A
substitute2 r e e' e'' =
  sem2 (ringP (ringP r)) (rotaPoly4 (rotaPoly4 Lit (Lit e))) (Lit e') e'' {-"~~."-}
\end{spec}

Consider the general case with substituting the |n| indeterminates in |e : PolyNn A| for |n| expressions, each of type |PolyN n A|.
%
Let |Vec B n| be the type of vectors (lists of fixed lengths) of length |n|.
%
A general |substitute| can be defined by:
\begin{spec}
substitute : ∀ {A} n -> Ring A -> PolyNn A -> Vec (PolyNn A) n -> PolyNn A
substitute {A} n r e es =
  sem (ringPS r n) n  (rotaOuter (n + n) n (liftPoly n (n + n) e))
                      (toDChain es) {-"~~,"-}
\end{spec}
where |liftPoly n m| (with |n{-"\!"-}<={-"\!"-}m|) lifts a |PolyN n A| to |PolyN m A| by applying |Lit|;
%
|rotaOuter (n + n) n|, as defined in Section \ref{sec:rotation}, composes |rotaPoly (n+n)| with itself |n| times, thereby moving the |n| original indeterminates of |e| to outermost positions;
%
the function |toDChain : ∀ {A} n -> Vec A n -> DChain A n| converts a vector to a descending chain, informally,
%
%format t0 = "\Varid{t}_0"
%format t0, = "\Varid{t}_0,"
%format t1 = "\Varid{t}_1"
%format t1, = "\Varid{t}_1,"
%format t2 = "\Varid{t}_2"
%format t2, = "\Varid{t}_2,"
\begin{spec}
toDChain [ t2, t1, t0 ] = (Lit (Lit t2), Lit t1, t0, tt) {-"~~;"-}
\end{spec}
%
%format PolyNmn = "\Varid{Poly}^{\Varid{m}+\Varid{n}}"
finally, |sem| performs the substitution.
%
Again, the actual code needs additional proof terms (to convince Agda that
|n{-"\!"-}<={-"\!"-}n+n|) and type coercion (between |PolyN n (PolyN m A)| and
|PolyNmn A|), which are omitted here.

\subsection{Expansion}

Expansion is an operation we put specific emphasis on, since it is
useful when implementing cryptosystems on microprocessors with no
native hardware support for arithmetic operations with polynomials or
integers of cryptographic sizes.
%
Let us use a simple yet specific example for further exposition:
%
the polynomial expression over complex numbers
$(3 + 2i) x^2 + (2 + i)x + 1$ can be represented by |Poly (Real ×
Real)|, whose semantics is a function |(Real × Real){-"\!"-}->{-"\!"-}(Real ×
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

It might turn out that |Real| is represented by a fixed number of
machine words: |Real{-"\!\!"-}={-"\!\!"-}WordN|.
%
As mentioned before, in cryptosystems |n| could be hundreds.
%
To compute the value of the polynomial, |Poly WordN| can be further
expanded to $|(PolyN n Word)|^\Varid{n}$, this time using arithmetic
operations defined for |Word|.
%
Now that each polynomial is defined over |Word|, whose arithmetic
operations are natively supported, we may compile the expressions,
in ways discussed in the next section, into a sequence of operations
in assembly language.
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
We define expansion in this section and compilation in
the next, as well as proving their correctness.
%
% Furthermore, expansion and it proof of correctness should take the
% arithmetic operation of its base type as parameters.
%

%format LitN1 = "\Varid{Lit}^{\Varid{n-1}}"
%format x1 = "\Varid{x}_1"
%format x2 = "\Varid{x}_2"
In general, a univariate polynomial over |n|-vectors, |Poly (Vec A n)|, can be
expanded to a |n|-vector of |n|-variate polynomial, |Vec (PolyN n A) n|. To
formally define expansion we need some helper functions. Firstly,
|genInd n| generates a vector |Ind ∷ Lit Ind ∷ ... LitN1 Ind ∷ []|. It corresponds
to expanding $x$ to $(x_1 , x_2)$ in the previous example.
\begin{spec}
genInd : ∀ {A} n → Vec (PolyN n A) n
genInd zero           = []
genInd (suc zero)     = Ind ∷ []
genInd (suc (suc n))  = Ind ∷ map Lit (genInd (suc n)) {-"~~."-}
\end{spec}
Secondly, |liftVal : ∀ {A} n → A → PolyNn A| lifts |A| to |PolyNn A| by |n| applications of |Lit|. The definition is routine.

Expansion can now be defined by:
\begin{spec}
expand : ∀ {A} n → Ring (Vec (PolyNn A) n) → Poly (Vec A n) → Vec (PolyNn A) n
expand n rv = foldP (genInd n) (map (liftVal n)) (fst rv)
\end{spec}
For the |Ind| case, one indeterminant is expanded to |n| using |genInd|.
%
For the |Lit xs| case, |xs : Vec A n| can be lifted to |Vec (PolyN n A) n| by
|map (liftVal n)|.
%
For addition and multiplication, we let |rv| decide how to combine vectors
of expressions.

The function |expand| alone does not say much --- all the complex work is done in |rv : Ring (Vec (PolyNn A) n)|. To generate |rv|, we define the type of operations that, given arithmetic operators for |A|, define ring instance for vectors of |A|:
\begin{spec}
RingVec : ℕ -> Set1
RingVec n = ∀ {A} -> Ring A -> Ring (Vec A n) {-"~~."-}
\end{spec}
%format addC = "(\mathbin{+_c})"
%format `addC` = "\mathbin{+_c}"
%format mulC = "(\mathbin{\times_c})"
%format `mulC` = "\mathbin{\times_c}"
%format ringP2 = "\Varid{ringP}^2"
For example, |rComplex| lifts arithmetic operations on |A| to
that of complex numbers over |A|:
\begin{spec}
rComplex : RingVec 2
rComplex ((+),(×), 𝟎 , 𝟏 , neg) = (addC , mulC , [𝟎, 𝟎], [𝟏 , 𝟎], negC)
  where  [ x1, y1 ] `addC` [ x2, y2 ] = [ x1 + x2, y1 + y2 ]
         [ x1, y1 ] `mulC` [ x2, y2 ] = [ x1 × x2 - y1 × y2 ,  x1 × y2 + x2 × y1 ]
         x - y = x + neg 𝟏 × y
         negC [ x, y ] = [ neg 𝟏 × x1, neg 𝟏 × y ] {-"~~."-}
\end{spec}
To expand a polynomial of complex numbers |Poly (Vec A 2)|, |expand| demands an instance of |Ring (Vec (PolyN 2 A) 2)|. One may thus call |expand 2 (rComplex (ringP2 r)|, where |r : Ring A|. That is, we use |rComplex| to combine a pair of polynomials, designating |((:+) , (:×))| as addition and multiplication.

\paragraph{Correctness.} Intuitively, |expand| is correct if the expanded
polynomial evaluates to the same value as that of the original. To
formally state the property, we have to properly supply all the needed ingredients. Consider |e : Poly (Vec A n)| --- a polynomial whose coefficients are vectors of length |n|. Let |r : Ring A| define arithmetic operators for |A|, and let |ringVec : RingVec n| define how arithmetic operators for elements are lifted to vectors. We say that |expand| is correct if, for all |xs : Vec A n|:
\begin{equation}
\begin{split}
  |sem1 (ringVec r) e xs =|~ & |map (\ e → sem r n e (toDChain xs))|\\
  &\qquad  |(expand n (ringVec (ringPS r n)) e)| \mbox{~~.}
\end{split}
\label{eq:expand-correct}
\end{equation}
On the lefthand side, |e| is evaluated by |sem1|, using operators supplied by |ringVec r|.
%
The value of the single indeterminant is |xs : Vec A n|, and the result also has type |Vec A n|.
%
On the righthand side, |e| is expanded to |Vec (PolyN n A) n|, for which
we need an instance of |Ring (Vec (PolyNn A) n)|, generated by
|ringVec (ringPS r n)|.
%
Each polynomial in the vector is then evaluated individually by |sem r n|.
%
The function |toDChain| converts a vector to a descending chain. The |n| elements in |xs| thus substitutes the |n| indeterminants of the expanded polynomial.

Interestingly, it turns out that |expand| is correct if |ringVec| is polymorphic --- that is, the way it computes vectors out of vectors depends only on the shape of its inputs, regardless of the type and values of their elements.
\begin{theorem} For all |n|, |e : Poly (Vec A n)|, |xs : Vec A n|,
|r : Ring A|, and |ringVec : RingVec|, property \eqref{eq:expand-correct} holds if |ringVec| is polymorphic.
\end{theorem}
\begin{proof}
Induction on |e|. For the base cases we need two lemmas:
\begin{itemize}
%\begin{lemma}\label{lma:sem-liftVal}
\item for all |n|, |x|, |es : DChain A n|, and |r|,
we have |sem r n (liftVal n x) es = x|;
%\end{lemma}
%\begin{lemma} \label{lma:sem-genInd}
\item for all |n|, |xs : Vec A n|, and |r : Ring A|, we have\\
|map (\ e → sem r n e (toDChain xs)) (genInd n) = xs|.
%\end{lemma}
\end{itemize}
%format addP = "({+_\Conid{VP}})"
%format `addP` = "\mathbin{+_\Conid{VP}}"
%format addA = "({+_\Conid{VA}})"
%format `addA` = "\mathbin{+_\Conid{VA}}"
The inductive case where |e := e1 :+ e2| eventually comes down to proving
that (abbreviating |\ e → sem r n e (toDChain xs)| to |sem'|):
\begin{spec}
map sem' (expand ringVec n e1) `addA` map sem' (expand ringVec n e2) =
  map sem' (expand ringVec n e1 `addP` expand ringVec n e2)
\end{spec}
where |addA = fst (fst (ringVec r))| defines addition on vectors of |A|'s, and |addP = fst (fst (ringVec (ringPS r n)))| on vectors of polynomials. But this is implied by the free theorem of |ringVec|. Specifically, |fst . fst . ringVec| has type
\begin{spec}
  {A : Set}  -> Ring A -> (Vec A n -> Vec A n -> Vec A n) {-"~~."-}
\end{spec}
The free theorem it induces is
%format add1 = "({+_1})"
%format `add1` = "\!\mathbin{+_1}\!"
%format add2 = "({+_2})"
%format `add2` = "\!\mathbin{+_2}\!"
%format addV1 = "({+_{\Conid{V}1}})"
%format `addV1` = "\!\mathbin{+_{\Conid{V}1}}\!"
%format addV2 = "({+_{\Conid{V}2}})"
%format `addV2` = "\!\mathbin{+_{\Conid{V}2}}\!"
%format mul1 = "({×_1})"
%format `mul1` = "\!\mathbin{×_1}\!"
%format mul2 = "({×_2})"
%format `mul2` = "\!\mathbin{×_2}\!"
%format z1 = "\Varid{𝟎}_1"
%format z2 = "\Varid{𝟎}_2"
%format one1 = "\Varid{𝟏}_1"
%format one2 = "\Varid{𝟏}_2"
%format neg1 = "\Varid{neg}_1"
%format neg2 = "\Varid{neg}_2"
%format x1 = "\Varid{x}_1"
%format x2 = "\Varid{x}_2"
%format y1 = "\Varid{y}_1"
%format y2 = "\Varid{y}_2"
%format ring1 = "\Varid{ring}_1"
%format ring2 = "\Varid{ring}_2"
\begin{spec}
∀ (X Y : Set) n ->
  ∀ (f : X -> Y) (ring1 : Ring X) (ring2 : Ring Y) -> P f ring1 ring2 ->
  ∀ (xs ys : Vec X n) ->
    let  addV1 = fst (fst (ringVec ring1))
         addV2 = fst (fst (ringVec ring2))
    in map f (xs `addV1` ys) = map f xs `addV2` map f ys {-"~~."-}
\end{spec}
The conclusion is exactly what we need, while |P| is given by:
\begin{spec}
P f (add1 , mul1 , z1 , one1 , neg1) (add2 , mul2 , z2 , one2 , neg2) =
  ∀ x1 x2 y1 y2 ->  f (x1 `add1` x2) = f x1 `add2` f x2  &&
                    f (x1 `mul1` x2) = f x1 `mul2` f x2 &&
                    f z1 = z2 && f one1 = one2 && f (neg1 x1) = neg2 (f x2) {-"~~."-}
\end{spec}
The case for |e := e1 :× e2| is similar.
\end{proof}

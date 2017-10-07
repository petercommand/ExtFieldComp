 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Operations on Polynomials}
\label{sec:operations}

Having defined a representation for multivariate polynomials, we ought to
demonstrate that this representation is feasible --- that we can define most of
the operations we want. In this section we show ...

\subsection{Rotation}

The first operation we consider swaps the two outermost indeterminates of an
|Expr2 A|, using |foldE|. It is perhaps instructive comparing it with
|litDist|.
\begin{spec}
rotaExpr2 : ∀ {A} → Expr2 A → Expr2 A
rotaExpr2 = foldE (Lit Ind) (foldE Ind (Lit ∘ Lit) ringE) ringE {-"~~."-}
\end{spec}
In |rotaExpr2|, the outermost |Ind| is replaced by |Lit Ind|. When
encountering |Lit e|, the inner |e| is lifted to |Expr2 A|. The |Ind| inside
|e| remains |Ind|, which becomes the outermost indeterminate after lifting.
Note that both |litDist| and |rotaExpr2| apply to |ExprN n A| for all |n ≥ 2|,
since |A| can be instantiated to an expression as well.

Consider |ExprN 3 A|, a polynomial with (at least) three indeterminates. To
"rotate" the three indeterminates, that is, turn |Lit Ind| to |Ind|, |Lit (Lit Ind)| to |Lit Ind|, and |Ind| to |LitN 3 Ind|, we could do:
\begin{spec}
  rotaExpr3 = fmap rotaExpr2 ∘ rotaExpr2 {-"~~,"-}
\end{spec}
where |fmap| is the usual ``map'' function:
\begin{spec}
  fmap : ∀ {A B} -> (A -> B) -> Expr A -> Expr B {-"~~."-}
\end{spec}
The first |rotaExpr2| swaps the two outer indeterminates, while |fmap rotaExpr2|
swaps the inner two. To rotate the outermost four indeterminates of an |ExprN 4 A|, we may define:
\begin{spec}
rotaExpr4 = fmap (fmap rotaExpr2) . rotaExpr3 {-"~~."-}
\end{spec}
In general, the following function rotates the first |n| indeterminates of
the given polynomial:%
\begin{spec}
rotaExprN : ∀ {A} (n : ℕ) → ExprNn A → ExprNn A
rotaExprN zero                 = id
rotaExprN (suc zero)           = id
rotaExprN (suc (suc zero))     = rotaExpr2
rotaExprN (suc (suc (suc n)))  = (fmapN (suc n)) rotaExpr2 . rotaExprN  (suc (suc n)) {-"~~."-}
\end{spec}
Note that in the actual Agda code we need to convince Agda that
|ExprN n (Expr A)| is the same type as |Expr (ExprN n A)| and use |subst|
to do type conversion. We omit the details here for clarity.

Given |m| and |n|, |rotaExprNm n m| compose |rotaExprN n| with itself
|m| times. Therefore, the first |n| indeterminates are rotated |m| times.
It will be handy in the next section.
\begin{spec}
rotaExprNm : ∀ {A} (n m : ℕ) → ExprNn A → ExprNn A
rotaExprNm n zero e = e
rotaExprNm n (suc m) e = rotaExprNm n m (rotaExprN n e) {-"~~."-}
\end{spec}

\subsection{Substitution}

%format substitute1 = "\Varid{substitute}_{1}"
%format substitute2 = "\Varid{substitute}_{2}"

Substitution is another operation one would expect. Given an expression |e|,
how do we substitute, for each occurrence of |Ind|, another expression |e'|,
using operations we have defined? Recalling that the type of
|semantics1| can be instantiated to |ExprN 2 A → Expr A → Expr A|, we may
lift |e| to |ExprN 2 A| by wrapping it with |Lit|, do a |rotaExpr2| to
expose the |Ind| inside |e|, and use |semantics1| to perform the
substitution:
\begin{spec}
substitute1 : ∀ {A} → Expr A → Expr A → Expr A
substitute1 e e' = semantics1 ringE (rotaExpr2 (Lit e)) e' {-"~~."-}
\end{spec}
What about |e : Expr2 A|? We may lift it to an |ExprN 4 A|, perform two
|rotaExpr4| to expose its two indeterminates, before using |semantics2|:
\begin{spec}
substitute2 :: ∀ {A} → Expr2 A -> Expr2 A -> Expr2 A -> Expr2 A
substitute2 e e' e'' =
  semantics2 ringE (rotaExpr4 . rotaExpr4 $ Lit (Lit e)) (Lit e') e'' {-"~~."-}
\end{spec}

We now consider the general case with |e : ExprN n A| and a vector of |n|
expressions, each of type |ExprN n A|.
(to do: can be simplified)
\begin{spec}
substitute : ∀ {A} n -> ExprNn A -> Vec (ExprNn A) n -> ExprNn A
substitute {A} n e e'
   = semantics {ExprN A n} {{toExprNumN {A} n}} n
        (subst id (sym (ExprN-comb {A} n n))
          (rotaExprN-m (n + n) n
             (liftExpr {_} {_} {n} {n + n}
               (≤→≤′ n (n + n) (≤-weakening n n n ≤-refl)) e)))
        (Vec→Nest n e')
\end{spec}

\subsection{Expansion}

Expansion is an operation we will put specific emphasis on, since its application
is what motivated us in the first place. As mentioned in
Section \ref{sec:introduction}, in cryptography we often have to deal with
polynomials over base types that are not just a number. For example,
the polynomial over complex numbers $(3 + 2i) x^2 + (2 + i)x + 1$
can be represented by |Expr (Real × Real)|, whose semantics is
a function |(Real × Real) -> (Real × Real)|. Let $x$ be $x_1 + x_2 i$, the
polynomial can be expanded as below:
\begin{align*}
  & (3 + 2i)(x_1 + x_2 i)^2 + (2 + i)(x_1 + x_2 i) + 1 \\
=~& (3 x^2_1 - 4 x_1 x_2 - 3 x^2_2) + (2 x^2_1 + 6 x_1 x_2 - 2 x^2_2) i +
  (2 x_1 - x_2) + (x_1 + 2 x_2) i + 1\\
=~& (3 x^2_1 + 2 x_1 - 4 x_1 x_2 - x_2 - 3 x^2_2 + 1) +
   (2 x^2_1 + x_1 + 6 x_1 x_2 + 2 x_2 - 2x^2_2) i \mbox{~~.}
\end{align*}
%format WordN = "\Varid{Word}^{\Varid{n}}"
That is, a univariate polynomial over pairs, |Expr (Real × Real)|, can be expanded to
|(Expr2 Real × Expr2 Real)|, a pair of bivariate expressions.
The expansion depends on the definitions of addition and multiplication of
complex numbers. It might turn out that |Real| is represented by a fixed
length of machine words, |Real = WordN|, and |Expr WordN| can be further
expanded to $|(ExprN n Word)|^\Varid{n}$, this time using arithmetic
operations defined for |Word|. Now that each polynomial is defined
over |Word|, whose arithmetic operation is supported by the machine, we may
compile the expressions, in ways discussed in the next section, into assembly
language. Such conversion and compilation are typically done by hand. We
would like to define expansion in this section and compilation in the next,
as well as proving their correctness. Furthermore, expansion and it proof of
correctness should take the arithmetic operation of its base type as parameters.

%format LitN1 = "\Varid{Lit}^{\Varid{n-1}}"
%format x1 = "\Varid{x}_1"
%format x2 = "\Varid{x}_2"
In general, a univariate polynomial of |n|-vectors, |Expr (Vec A n)|, can be
expanded to a |n|-vector of |n|-variate polynomial, |Vec (ExprN n A) n|. To
formally define expansion we need some helper functions. Firstly,
|genInd n| generates a vector |Ind ∷ Lit Ind ∷ ... LitN1 Ind ∷ []|. It corresponds
to expanding |x| to |(x1 , x2)|.
\begin{spec}
genInd : ∀ {A} n → Vec (ExprN n A) n
genInd zero           = []
genInd (suc zero)     = Ind ∷ []
genInd (suc (suc n))  = Ind ∷ (map Lit (genInd (suc n))) {-"~~."-}
\end{spec}
Secondly, |liftVal : ∀ {A} n → A → ExprNn A| lifts |A| to |ExprNn A| by applying
|Lit| to it |n| times. The definition is routine. Finally, we need an operation
defining arithmetic operators for a vector of |A|, given arithmetic operators
for |A|. We give such operations a type:
\begin{spec}
RingVec : Set1
RingVec = ∀ {A} n -> Ring A -> Ring (Vec A n) {-"~~."-}
\end{spec}

Expansion can now be defined by:
\begin{spec}
expand : ∀ {A} n → RingVec → Expr (Vec A n) → Vec (ExprN n A) n
expand ringVec n = foldE (genInd n) (map (liftVal n)) (ringVec ringE) {-"~~."-}
\end{spec}
For the |Ind| case, one indeterminant is expanded to |n| using |genInd|. For the
|Lit xs| case, |xs : Vec A n| can be lifted to |Vec (ExprN n A) n| by |map (liftVal n)|.
For addition and multiplication, we let |ringVec| decide how to combine vectors
of expressions, but specifying |((:+), (:×))| as atomic operations.

\paragraph{Correctness of |expand|}

\begin{lemma}\label{lma:sem-liftVal}
For all |n|, |x|, |es : Tele A n|, and |r : Ring A|,
we have |semantics r n (liftVal n x) es = x|.
\end{lemma}

\begin{lemma} \label{lma:sem-genInd}
For all |n|, |xs : Vec A n|, and |r : Ring A|, we have
|map (\ e → semantics r n e (toTele xs)) (genInd n) = xs|.
\end{lemma}

\begin{theorem} For all |n|, |e : Expr (Vec A n)|, |xs : Vec A n|,
|r : Ring A|, and |ringVec : RingVec|, we have
\begin{spec}
  semantics1 (ringVec r) e xs =
    map (\ e → semantics r n e (toTele xs)) (expand ringVec n e) {-"~~,"-}
\end{spec}
if |ringVec| is polymorphic.
\end{theorem}

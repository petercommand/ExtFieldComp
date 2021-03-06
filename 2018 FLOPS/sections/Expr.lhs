%include agda.fmt
%include Formatting.fmt

\section{Univariate and Multivariate Polynomials}
\label{sec:expressions}

In this section, we present our representation for univariate and
multivariate polynomials, as well as their semantics.
%
The following Agda datatype denotes a univariate polynomial whose coefficients are of type |A|:%
\footnote{We use Haskell convention that infix data constructors start with
a colon and, for concise typesetting, write |(:+)| instead of the Agda notation $\_$|:+|$\_$.
%
In the rest of the paper we also occasionally use Haskell syntax for brevity.
}
\begin{spec}
data Poly (A : Set) : Set where
  Ind   : Poly A
  Lit   : A -> Poly A
  (:+)  : Poly A -> Poly A -> Poly A
  (:×)  : Poly A -> Poly A -> Poly A {-"~~,"-}
\end{spec}
where |Ind| denotes the indeterminate, |Lit| denotes a constant (of type |A|), while |(:+)| and |(:×)| respectively denote addition and multiplication. A polynomial $2 x^2 + 3x + 1$ can be represented by the following expression
of type |Poly ℤ|:
\begin{spec}
 (Lit 2 :× Ind :× Ind) :+ (Lit 3 :× Ind) :+ Lit 1 {-"~~."-}
\end{spec}
Notice that the type parameter |A| is abstracted over the type of coefficients.
%
This allows us to represent polynomials whose coefficients have non-simple
types --- in particular, polynomials whose coefficients are themselves
polynomials.
%
Do not confuse this with the more conventional representation of arithmetic
expressions:
\begin{spec}
data Expr A = Var A | Lit Int | Expr A :+ Expr A | Expr A :× Expr A {-"~~,"-}
\end{spec}
where the literals are usually assigned a fixed type (in this example, |Int|), and the type parameter is abstracted over variables |Var|.

%In this section, we shall elaborate on what we mean by
%Equation~\ref{eq:datatype} in Section~\ref{sec:introduction}.

% Recall the categorical style outlined by Bird and de
% Moor~\cite{DBLP:books/daglib/0096998} and consider the following
% recursively defined datatype that denotes univariate polynomials
% over type $R$:
% %
% \[ expr\,R ::= ind \mid lit\,R \mid add\ (expr\,R,expr\,R) \mid mul\
%   (expr\,R,expr\,R). \]
% %
% This declares $[ind,lit,add,mul]_R:F(R,expr\,R)\rightarrow expr\ R$ as
% the initial algebra of the functor $F(R,\cdot)$, where
% $F(A,B)=1+A+(B\times B)+(B\times B)$ as defined in
% Equation~\ref{eq:datatype}.
% %
% The datatype $expr\,R$ is a tree having two kinds of leaf nodes,
% $ind$ and $lit\,R$, respectively representing the indeterminate $X$ itself and
% constants from $R$.
% %
% Furthermore, there are two ways to join two such binary trees, i.e.,
% $add$ and $mul$, respectively representing the addition and multiplication
% operations in $R[X]$.
% %
% Clearly, each instance of such binary tree corresponds to the syntax
% tree of a univariate polynomial from $R[X]$.
% %
% Naturally, the categorical-style definition of the datatype $expr\,R$
% gives induces a catamorphisms (a $\mi{fold}$),
% i.e.,
% \begin{equation} \label{eq:catamorphism}
%   \cata{f_i,f_\ell,f_a,f_m} % =fold\ (f_i,f_\ell,f_a,f_m)
%     : expr\,R\rightarrow S, \end{equation} where $f_i : 1\rightarrow S$,
% $f_\ell : R\rightarrow S$, $f_a : S\rightarrow S\rightarrow S$, and
% $f_m : S\rightarrow S\rightarrow S$.
% %
% This allows us to derive various functions in an economical way.

\subsection{Univariate Polynomial and its Semantics}

%format e1 = "\Varid{e}_{1}"
%format e2 = "\Varid{e}_{2}"

In the categorical style outlined by Bird and de Moor~\cite{DBLP:books/daglib/0096998}, every {\em regular} datatype gives rise to a {\em fold}, also called a {\em catamorphism}.
%
The type |Poly| induces a fold that, conventionally, takes four arguments, each replacing one of its four constructors.
%
To facilitate our discussion later, we group the last two arguments together.
%
The fold for |Poly| is thus given by:
\begin{spec}
foldP :  {A B : Set} -> B -> (A -> B) ->
         ((B -> B -> B) × (B -> B -> B)) -> Poly A -> B
foldP x f ((oplus),(otimes))  Ind         = x
foldP x f ((oplus),(otimes))  (Lit y)     = f y
foldP x f ((oplus),(otimes))  (e1 :+ e2)  =  foldP x f ((oplus),(otimes)) e1 oplus
                                             foldP x f ((oplus),(otimes)) e2
foldP x f ((oplus),(otimes))  (e1 :× e2)  =  foldP x f ((oplus),(otimes)) e1 otimes
                                             foldP x f ((oplus),(otimes)) e2 {-"~~,"-}
\end{spec}
where arguments |x|, |f|, |(oplus)|, and |(otimes)| respectively replace constructors |Ind|, |Lit|, |(:+)|, and |(:×)|.

\paragraph{Evaluation.} To evaluate a polynomial of type |Poly A|, we have to
know how to perform arithmetic operations for type |A|. Define
\begin{spec}
Ring : Set -> Set
Ring A =  ((A -> A -> A) × (A -> A -> A)) × A × A × (A -> A) {-"~~,"-}
\end{spec}
the intention is that the tuple |Ring A| defines addition, multiplication, zero, one, and negation for |A|
%
(addition and multiplication are grouped together, for our convenience later).
%
% \footnote{While we do expect all the ring properties such as existence of
% additive identity, inverse, and distributivity, etc., to hold, we do not
% enforce them in this datatype.}
%
In our Haskell implementation, |Ring| is a type class for types whose addition and multiplication are defined.
%
It can usually be inferred what instance of |Ring| to use.
%
When proving properties about |foldP|, however, it is
clearer to make the construction of |Ring| instances explicit.

With the presence of |Ind|, the semantics of |Poly A| should be |A → A| --- a function that takes the value of the indeterminate and returns a value.
%
We define the following operation that lifts pointwise the addition and multiplication of some type |B| to |A → B|:
\begin{spec}
ring→ : ∀ {A B} → Ring B → Ring (A → B)
ring→ (((+),(×)),𝟎,𝟏,neg) =
  ((\ f g x -> f x + g x, \ f g x -> f x × g x), const 𝟎, const 𝟏, (neg .)) {-"~~,"-}
\end{spec}
where |const x y = x|.
The semantics of a univariate polynomial is thus given by:
\begin{spec}
sem1 : ∀ {A} → Ring A → Poly A → A → A
sem1 rng = foldP id const (fst (ring→ rng)) {-"~~,"-}
\end{spec}
where |id x = x| and |fst| retrieves the left component of a pair.

%format Ind1 = "\Conid{Ind}_{1}"
%format Ind2 = "\Conid{Ind}_{2}"

\subsection{Bivariate Polynomials}

To represent polynomials with two indeterminates, one might extend
|Poly| with a constructor |Ind'| in addition to |Ind|.
%
It turns out to be unnecessary --- it is known that the bivariate
polynomial ring $R[X,Y]$ is isomorphic to $R[X][Y]$ (modulo the operation |litDist|, to be defined later).
%
That is, a polynomial over base ring |A| with two indeterminates can be
represented by |Poly (Poly A)|.

To understand the isomorphism, consider the following expression:
\begin{spec}
e : Poly (Poly ℤ)
e = (Lit (Lit 3) :× Ind :× Lit (Ind :+ Lit 4)) :+ Lit Ind :+ Ind {-"~~."-}
\end{spec}
Note that to represent a literal |3|, we have to write |Lit (Lit 3)|, since
the first |Lit| takes a |Poly ℤ| as its argument. To evaluate |e| using
|sem1|, we have to define |Ring (Poly ℤ)|. A natural choice is to connect
two expressions using corresponding constructors:
\begin{spec}
ringP  : ∀ {A} → Ring A → Ring (Poly A)
ringP (_ , 𝟎 , 𝟏 , neg) = (((:+), (:×)) , Lit 𝟎 , Lit 𝟏 , (Lit (neg 𝟏) :x)) {-"~~."-}
\end{spec}
With |ringP| defined, |sem1 (ringP r) e| has type |Poly A → Poly A|.
Evaluating, for example |sem1 (ringP r) e (Ind :+ Lit 1)|, yields
\begin{spec}
e' : Poly ℤ
e' = (Lit 3 :× (Ind :+ Lit 1) :× (Ind :+ Lit 4)) :+ Ind :+ (Ind :+ Lit 1) {-"~~."-}
\end{spec}
Note that |Lit Ind| in |e| is replaced by the argument |Ind :+ Lit 1|.
Furthermore, one layer of |Lit| is removed, thus both |Lit 3| and |Ind :+ Lit 4| are exposed to the outermost level.
%
The expression |e'| may then be evaluated by |sem1 rngℤ|, where |rngℤ : Ring ℤ|.
%
The result is a natural number.
%
In general, the function |sem2| that evaluates |Poly (Poly A)| can be defined by:
\begin{spec}
sem2 : ∀ {A} → Ring A → Poly (Poly A) → Poly A → A → A
sem2 r e2 e1 x = sem1 r (sem1 (ringP r) e2 e1) x {-"~~."-}
\end{spec}

This is how |Poly (Poly ℤ)| simulates bivariate polynomials: the two
indeterminates are respectively represented by |Ind| and |Lit Ind|.
%
During evaluation, |Ind| can be instantiated to an expression |arg| of type |Poly ℤ|, while |Lit Ind| can be instantiated to a |ℤ|.
%
If |arg| contains |Ind|, it refers to the next indeterminate.

What about expressions like |Lit (Ind :+ Lit 4)|?
%
One can see that its semantics is the same as |Lit Ind :+ Lit (Lit 4)|, the expression we get by pushing |Lit| to the leaves.
%
In general, define the following function:
\begin{spec}
litDist : ∀ {A} → Poly (Poly A) → Poly (Poly A)
litDist = foldP Ind (foldP (Lit Ind) (Lit ∘ Lit) ((:+), (:×))) ((:+), (:×)) {-"~~."-}
\end{spec}
The function traverses through the given expression and, upon encountering
a subtree |Lit e|, lifts |e| to |Poly (Poly A)| while distributing |Lit| inwards |e|.
%
We can prove the following theorem:
\begin{theorem} For all |e : Poly (Poly A)| and |r : Ring A|, we have
|sem2 r (litDist e) = sem2 r e|.
\end{theorem}

\subsection{Multivariate Polynomials}
In general, as we have mentioned in Section~\ref{sec:introduction}, the
multivariate polynomial $R[X_1,X_2\ldots,X_m]$ is isomorphic to
univariate polynomial ring $S[X_m]$ over the base ring
$S=R[X_1,X_2,\ldots,X_{m-1}]$ (modulo the distribution law of |Lit|).
%
That is, a polynomial over |A| with |n| indeterminates can be represented by |PolyN n A|, defined by
\begin{spec}
PolyN zero     A = A
PolyN (suc n)  A = Poly (PolyN n A) {-"~~."-}
\end{spec}

To define the semantics of |PolyN n A|, recall that, among its |n| indeterminates, the outermost indeterminate shall be instantiated to an expression of type |PolyN (n-1) A|, the next indeterminate to |PolyN (n-2) A|..., and the inner most indeterminate to |A|, before yielding a value of type |A|.
%
Define
\begin{spec}
DChain : Set -> ℕ -> Set
DChain A zero     = ⊤
DChain A (suc n)  = PolyNn A × DChain A n {-"~~,"-}
\end{spec}
that is, |DChain A n| (the name standing for a ``descending chain'') is a list of |n| elements, with the first having type |PolyN (n-1) A|, the second |PolyN (n-2) A|, and so on. The type |⊤| denotes the ``unit'' type, inhabited by exactly one term |tt|.

Given an implementation of |Ring A|, the semantics of |PolyN n A| is a function |DChain A n -> A|, defined inductively as below:
\begin{spec}
sem : ∀ {A} -> Ring A -> (n : ℕ) -> PolyNn A -> DChain A n -> A
sem r zero     x  tt        = x
sem r (suc n)  e  (t , es)  = sem r n (sem1 (ringPS r n) e t) es {-"~~,"-}
\end{spec}
where |ringPS| delivers the |Ring (PolyN n A)| instance for all |n|:
\begin{spec}
ringPS : ∀ {A} → Ring A → ∀ n → Ring (PolyN n A)
ringPS r zero     = r
ringPS r (suc n)  = ringP (ringPS r n) {-"~~."-}
\end{spec}
For |n := 2| and |3|, for example, |sem r n| expands to:
%format t0 = "\Varid{t}_0"
%format t0, = "\Varid{t}_0,"
%format t1 = "\Varid{t}_1"
%format t1, = "\Varid{t}_1,"
%format t2 = "\Varid{t}_2"
%format t2, = "\Varid{t}_2,"
%format ringP2 = "\Varid{ringP}^2"
%format ringPi = "\Varid{ringP}^i"
\begin{spec}
sem r 2 e (t1, t0, tt)      = sem1 r (sem1 (ringP r) e t1) t0
                            = (sem1 r . sem1 (ringP r) e) t1 t0{-"~~,"-}
sem r 3 e (t2, t1, t0, tt)  = sem1 r (sem1 (ringP r) (sem1 (ringP2 r) e t2) t1) t0
                            = (sem1 r . sem1 (ringP r) . sem1 (ringP2 r) e) t2 t1 t0 {-"~~."-}
\end{spec}
Essentially, |sem r n| is |n|-fold composition of |sem1 (ringPi r)|,
each interpreting one level of the given expression.

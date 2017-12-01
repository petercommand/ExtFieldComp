 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt

\section{Univariate and Multivariate Polynomials}
\label{sec:expressions}

In this section we present our representation for univariate and
multivariate polynomials, and their semantics.
%
The following Agda datatype denotes a univariate polynomial whose coefficients are of type |A|:%
\footnote{We use Haskell convention that infix data constructors start with
a colon and, for a more concise typesetting, write |(:+)| instead of the Agda notation $\_$|:+|$\_$.
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
where |Ind| denotes the indeterminate, |Lit| denotes a constant (of type |A|), while |(:+)| and |(:×)| respectively denote addition and multiplication. A polynomial $2 x^2 + 3x + 1$ could be denoted by the following expression
of type |Poly ℕ|:
\begin{spec}
 (Lit 2 :× Ind :× Ind) :+ (Lit 3 :× Ind) :+ Lit 1 {-"~~."-}
\end{spec}
Notice that the type parameter |A| is abstracted over the type of coefficients. This allows us to represent polynomials whose coefficient are of complex types --- in particular, polynomials whose coefficients are themselves polynomials. Do not confuse this with the more conventional representation of arithmetic expressions:
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
To facilitate our discussion later, we group the last two arguments together and define:
\begin{spec}
Ring : Set -> Set
Ring A = (A -> A -> A) × (A -> A -> A) {-"~~."-}
\end{spec}
The intention is that |Ring A| is a pair of binary operators that defines addition and multiplication for values of type |A|.%
\footnote{While we do expect all the ring properties such as existence of
additive identity, inverse, and distributivity, etc., to hold, we do not
enforce them in this datatype.} We then define the fold for |Poly|:
\begin{spec}
foldP : ∀ {A B : Set} -> B -> (A -> B) -> Ring B -> Poly A -> B
foldP x f rng                 Ind         = x
foldP x f rng                 (Lit y)     = f y
foldP x f ((oplus),(otimes))  (e1 :+ e2)  =  foldP x f ((oplus),(otimes)) e1 oplus
                                             foldP x f ((oplus),(otimes)) e2
foldP x f ((oplus),(otimes))  (e1 :× e2)  =  foldP x f ((oplus),(otimes)) e1 otimes
                                             foldP x f ((oplus),(otimes)) e2 {-"~~."-}
\end{spec}
In our Haskell implementation, |Ring| is a type class for types whose addition and multiplication are defined. When |foldP| is called, it can usually be inferred what instance of |Ring| to use.
%
When proving properties about |foldP|, however, it is
clearer to make the construction of |Ring| instances explicit.

\paragraph{Evaluation.} Assuming a base type |A| for which |Ring A| is defined,
consider evaluating a polynomial of type |Poly A|.
%
With the presence of |Ind|, the semantics of |Poly A| should be |A → A| --- a function that takes the value of the indeterminate and returns a value.

We define the following operation that lifts pointwise the addition and multiplication of some type |B| to |A → B|:
\begin{spec}
ring→ : ∀ {A B} → Ring B → Ring (A → B)
ring→ ((+),(×)) = (  \ f g x -> f x + g x,
                     \ f g x -> f x × g x) {-"~~."-}
\end{spec}
The semantics of a univariate polynomial is thus given by:
\begin{spec}
sem1 : ∀ {A} → Ring A → Poly A → A → A
sem1 rng = foldP id const (ring→ rng) {-"~~."-}
\end{spec}

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

To see how that works, consider the following expression:
\begin{spec}
e : Poly (Poly ℕ)
e = (Lit (Lit 3) :× Ind :× Lit (Ind :+ Lit 4)) :+ Lit Ind :+ Ind {-"~~."-}
\end{spec}
Note that |Lit| in the first level takes |Poly ℕ| as arguments, thus to
represent a literal |3| we have to write |Lit (Lit 3)|. To evaluate |e| using
|sem1|, we have to define |Ring (Poly ℕ)|. A natural choice is to connect
two expressions using corresponding constructors:
\begin{spec}
ringP  : ∀ {A} → Ring (Poly A)
ringP  = ((:+), (:×)) {-"~~."-}
\end{spec}
With |ringP| defined, |sem1 ringP e| has type |Poly A → Poly A|.
Evaluating, for example |sem1 ringP e (Ind :+ Lit 1)|, yields
\begin{spec}
e' : Poly ℕ
e' = (Lit 3 :× (Ind :+ Lit 1) :× (Ind :+ Lit 4)) :+ Ind :+ (Ind :+ Lit 1) {-"~~."-}
\end{spec}
Note that |Lit Ind| in |e| is replaced by the argument |Ind :+ Lit 1|.
Furthermore, one layer of |Lit| is removed, thus both |Lit 3| and |Ind :+ Lit 4| are exposed to the outermost level.
%
The expression |e'| may then be evaluated by |sem1 rngℕ|, where |rngℕ : Ring ℕ|.
%
The result is a natural number.
%
In general, the function |sem2| that evalulates |Poly (Poly A)| can be defined by:
\begin{spec}
sem2 : ∀ {A} → Ring A → Poly (Poly A) → Poly A → A → A
sem2 r e2 e1 x = sem1 r (sem1 ringP e2 e1) x {-"~~."-}
\end{spec}

This is how |Poly (Poly ℕ)| simulates bivariate polynomials: the two
indeterminates are respectively represented by |Ind| and |Lit Ind|.
%
During evaluation, |Ind| can be instantiated to an expression |arg| of type |Poly ℕ|, while |Lit Ind| can be instantiated to a |ℕ|.
%
If |arg| contains |Ind|, it refers to the next indeterminate.

What about subexpressions like |Lit (Ind :+ Lit 4)|?
%
One can see that its semantics is the same as |Lit Ind :+ Lit (Lit 4)|, the expression we get by pushing |Lit| to the leaves.
%
In general, define the following function:
\begin{spec}
litDist : ∀ {A} → Poly (Poly A) → Poly (Poly A)
litDist = foldP Ind (foldP (Lit Ind) (Lit ∘ Lit) ringP) ringP {-"~~."-}
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
that is, |DChain A n| (the name standing for a ``descending chain'') is a list of |n| elements, with the first having type |PolyN (n-1) A|, the second |PolyN (n-2) A|, and so on.

Given an implementation of |Ring A|, the semantics of |PolyN n A| is a function |DChain A n -> A|, defined inductively as below (where |tt| is the only term having type |⊤|):
\begin{spec}
sem : ∀ {A} -> Ring A -> (n : ℕ) -> PolyNn A -> DChain A n -> A
sem r zero     x  tt        = x
sem r (suc n)  e  (t , es)  = sem r n (sem1 (ringPS r) e t) es {-"~~,"-}
\end{spec}
where |ringPS| delivers the |Ring (PolyN n A)| instance for all |n|:
\begin{spec}
ringPS : ∀ {A} → Ring A → ∀ {n} → Ring (PolyN n A)
ringPS r zero     = r
ringPS r (suc n)  = ringP {-"~~."-}
\end{spec}
For |n := 2| and |3|, for example, |sem r n| expands to:
%format t0 = "\Varid{t}_0"
%format t0, = "\Varid{t}_0,"
%format t1 = "\Varid{t}_1"
%format t1, = "\Varid{t}_1,"
%format t2 = "\Varid{t}_2"
%format t2, = "\Varid{t}_2,"
\begin{spec}
sem r 2 e (t1, t0, tt)      = sem1 r (sem1 ringP e t1) t0 {-"~~,"-}
sem r 3 e (t2, t1, t0, tt)  = sem1 r (sem1 ringP (sem1 ringP e t2) t1) t0 {-"~~."-}
\end{spec}
Essentially, |sem r n| is |n|-fold composition of |sem1 (ringPS r)|,
each interpreting one level of the given expression.

% \vspace{1cm}
% {\bf Old contents below}
%
% For example, it is natural to define the semantics of a polynomial
% $f\in R[X]$ as the corresponding \emph{polynomial function}
% $\tilde f:R\rightarrow R$ that sends $x\in R$ to $f(x)\in R$.
% %
% In this case, we let $S=R\rightarrow R$ in
% Equation~\ref{eq:catamorphism}:
% \[ semantics = fold\ (id_R,const_R,+,\times), \] where
% $+ : (R\rightarrow R)\rightarrow (R\rightarrow R)\rightarrow
% (R\rightarrow R)$ sums two polynomial functions point-wise, and
% similarly $\times$, multiplies point-wise.
% %
% From here, we can see that in general, it is nature to require the
% datatype $S$ to behave like a ring in order to have a ``reasonably
% natural'' catamorphism.
% %
%
% %
% The situation for multivariate polynomials is similar but a bit more
% complicated.
% %
% Ideally, the semantics of a bivariate polynomial should be a (curried)
% function of type $R\rightarrow R\rightarrow R$, i.e., the semantics
% function should have the type
% $expr\ (expr\ R)\rightarrow R\rightarrow R\rightarrow R$.
% %
% Now if we apply the $semantics$ function for univariate polynomials to
% something of type $expr\ (expr\ R)$, we get something of type
% $expr\ R\rightarrow expr\ R$.
% %
% Intuitively, this says that the ``semantics'' of $f(X,Y)\in R[X][Y]$
% is a \emph{polynomial-valued} function
% $f(X,\cdot) : R[X]\rightarrow R[X]$ that maps a polynomial
% $g(X))\in R[X]$ to $f(X,g(X))\in R[X]$.
% %
% Then the semantics of $f(X,g(X))$ is of type $R\rightarrow R$,
% suggesting that $semantics\circ (semantics\ f)$ may be a good starting
% point for defining the semantics of a bivariate polynomial $f$.
% %
%
% %
% Let us denote $expr\ (expr\ R)$ as $expr^2\ R$ and
% $semantics\circ (semantics\ f)$ as $semantics_2\ f$.
% %
% Then from the above discussion, $semantics_2\ f$ is of type
% $expr\ R\rightarrow R\rightarrow R$, which is strictly more than what
% we want because $R$ is a proper subset of $expr\ R$.
% %
% Therefore, when we ``evaluate'' the semantics of a bivariate
% polynomial $f\in R[X,Y]$ as a bivariate polynomial function (they
% are!) at a point, we would need to ``lift'' one of the coordinates and
% regard it as a univariate polynomial.
% %
% Another minor nuisance is that we would need to feed the arguments to
% $semantics_2\ f$ in an order \emph{opposite} to the natural order.
% %
% That is, to evaluate the (ideal) semantics of a bivariate polynomial
% $f(X,Y)\in R[X,Y]$, we would need to compute
% $semantics_2\ f\ (lit\ y)\ x$.
% %
%
% %
% In general, we can recursively define $semantics_{n+1}\ f$ as
% \[ semantics\circ(semantics_n\ f) \] for $n\geq 1$.
% %
% Again we would need appropriate lifting and order reversing when
% evaluating the semantics of a multivariate polynomial
% $f(X_1,\ldots,X_n)\in R[X_1,\ldots,X_n]$ at a point
% $(x_1,\ldots,x_n)\in R^n$ by computing
% $semantics_n\ f\ (lit^{n-1}\ x_n)\ \cdots\ x_1$.
% %
%
% %
% We can also define
% $substitute : expr\ R\rightarrow expr\ R\rightarrow expr\ R$ in a
% similar way using $fold$.
% %
% Intuitively, it should take two polynomials $f(X),g(X)\in R[X]$ and
% substitute say $g(X)$ into $f(X)$ by replacing every occurence of $X$
% in $f$ with $g(X)$.
% %
% If we ``inject'' $f(X)$ into $R[\_,X]$ and regard it as a bivariate
% polynomial $f'(\_,X)$ in which the other indeterminate never occurs,
% then the polynomial-valued function
% $semantics\ f' : expr\ R\rightarrow expr\ R$ seems useful now.
% %
% That is, $semantics\ f'\ g$ would compute $f(g(X))$, which is
% precisely what we want as $substitute\ f\ g$.
% %
% The only thing we need here is the ``injection'' function that, in
% this case, injects univariate polynomials into a bivariate polynomial
% ring.
% %
% Similar to $semantics$, we can also generalize $substitute$ to
% $substitute_n : expr^n\ R\rightarrow\cdots\rightarrow expr^n R$ for
% $n>1$ by appropriately injection and lifting.
% %
% Take $n=2$ as an example: to get $f(g_1(X,Y),g_2(X,Y))$ for
% $f,g_1,g_2\in R[X,Y]$, we can compute
% $substitute_2\ f\ g_1\ g_2=semantics_2\ f'\ g_2'\ g_1$, where
% $f'\in R[\_,\_,X,Y]$ is the injection of $f$, and $g_2'=lit\ g_2$ is
% the lifting of $g_2$ as discussed earlier in this section.
% %

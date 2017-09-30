 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt

\section{Univariate and Multivariate Polynomials}
\label{sec:expressions}

In this section we present our representation for univariate and
multivariate polynomials, and their semantics.
%In this section, we shall elaborate on what we mean by
%Equation~\ref{eq:datatype} in Section~\ref{sec:introduction}.

Recall the categorical style outlined by Bird and de
Moor~\cite{DBLP:books/daglib/0096998} and consider the following
recursively defined datatype that denotes univariate polynomials
over type $R$:
%
\[ expr\,R ::= ind \mid lit\,R \mid add\ (expr\,R,expr\,R) \mid mul\
  (expr\,R,expr\,R). \]
%
This declares $[ind,lit,add,mul]_R:F(R,expr\,R)\rightarrow expr\ R$ as
the initial algebra of the functor $F(R,\cdot)$, where
$F(A,B)=1+A+(B\times B)+(B\times B)$ as defined in
Equation~\ref{eq:datatype}.
%
The datatype $expr\,R$ is a tree having two kinds of leaf nodes,
$ind$ and $lit\,R$, respectively representing the indeterminate $X$ itself and
constants from $R$.
%
Furthermore, there are two ways to join two such binary trees, i.e.,
$add$ and $mul$, respectively representing the addition and multiplication
operations in $R[X]$.
%
Clearly, each instance of such binary tree corresponds to the syntax
tree of a univariate polynomial from $R[X]$.
%
Naturally, the categorical-style definition of the datatype $expr\,R$
gives induces a catamorphisms (a $\mi{fold}$),
i.e.,
\begin{equation} \label{eq:catamorphism}
  \cata{f_i,f_\ell,f_a,f_m} % =fold\ (f_i,f_\ell,f_a,f_m)
    : expr\,R\rightarrow S, \end{equation} where $f_i : 1\rightarrow S$,
$f_\ell : R\rightarrow S$, $f_a : S\rightarrow S\rightarrow S$, and
$f_m : S\rightarrow S\rightarrow S$.
%
This allows us to derive various functions in an economical way.

\subsection{Univariate Polynomial and its Semantics}

In Agda, the datatype can be expressed by the following declaration:%
\footnote{We use Haskell convention that infix data constructors start with
a colon and, for a more concise typesetting, write |(:+)| instead of the Agda
notation $\_$|:+|$\_$.}
\begin{spec}
data Expr (A : Set) : Set where
  Ind   : Expr A
  Lit   : A -> Expr A
  (:+)  : Expr A -> Expr A -> Expr A
  (:×)  : Expr A -> Expr A -> Expr A {-"~~."-}
\end{spec}
%format e1 = "\Varid{e}_{1}"
%format e2 = "\Varid{e}_{2}"
As a convention, the $\mi{fold}$ it induces usually takes four arguments, each
replacing one of the four constructors. To facilitate our discussion later,
we group the last two together and define:
\begin{spec}
Ring : Set -> Set
Ring A = (A -> A -> A) × (A -> A -> A) {-"~~."-}
\end{spec}
That is, |Ring A| is a pair of binary operators that defines how to perform addition
and multiplication for values of type |A|.%
\footnote{While we do expect all the ring properties such as existence of
additive identity, inverse, and distributivity, etc., to hold, we do not
enforce them in this datatype.} We then define the $\mi{fold}$ for |Expr|:
\begin{spec}
foldE : ∀ {A B : Set} -> B -> (A -> B) -> Ring B -> Expr A -> B
foldE x f rng        Ind         = x
foldE x f rng        (Lit y)     = f y
foldE x f ((+),(×))  (e1 :+ e2)  =  foldE x f ((+),(×)) e1 +
                                    foldE x f ((+),(×)) e2
foldE x f ((+),(×))  (e1 :× e2)  =  foldE x f ((+),(×)) e1 ×
                                    foldE x f ((+),(×)) e2 {-"~~."-}
\end{spec}
In our Haskell implementation, |Ring| is a type class for types whose addition
and multiplication are defined, and it can usually be inferred what instance of
|Ring| to use. When proving properties about |foldE|, it is sometimes
clearer to make the construction of |Ring| instances explicit.

\paragraph{Evaluation} Assuming a base type |A| for which |Ring A| is defined,
consider evaluating a polynomial of type |Expr A|. Without the presence of
constructor |Ind|, |Expr A| is an expresson without a variable, and evaluating
it is simply a matter of folding over the expression using |Ring A|. With |Ind|,
however, the semantics of |Expr A| should be |A → A| --- a function
that takes the value of the indeterminate and returns a value.

We define the following operation that lifts the addition and multiplication
of some type |B| to |A → B|:
\begin{spec}
ring→ : ∀ {A B : Set} → Ring B → Ring (A → B)
ring→ ((+),(×)) = (  \ f g x -> f x + g x,
                     \ f g x -> f x × g x) {-"~~."-}
\end{spec}
The semantics of a univariate polynomial is thus given by:
\begin{spec}
semantics1 : ∀ {A} → Ring A → Expr A → A → A
semantics1 rng = foldE id const (ring→ rng) {-"~~."-}
\end{spec}

%format Ind1 = "\Conid{Ind}_{1}"
%format Ind2 = "\Conid{Ind}_{2}"

\subsection{Bivariate Polynomials}

To represent polynomials with two indeterminates, we could extend
|Expr| with an additional constructor |Ind'| in addition
to |Ind|. It turns out to be unnecessary: a polynomial over base ring
|A| with two indeterminates can be represented by |Expr (Expr A)|.

For an example, consider the following expression of type |Expr (Expr ℕ)|:
\begin{spec}
  e = Lit (Lit 3) :× Ind :× Lit (Ind :+ Lit 4) :+ Lit Ind :+ Ind {-"~~."-}
\end{spec}
Note that |Lit| in the first level takes |Expr ℕ| as arguments, thus to
represent a literal |3| we have to write |Lit (Lit 3)|. To evaluate |e| using
|semantics1|, we have to define |Ring (Expr ℕ)|. A natural choice is to connect
two expressions using corresponding constructors:
\begin{spec}
ringE : ∀ {A} → Ring (Expr A)
ringE = ((:+), (:×)) {-"~~."-}
\end{spec}
With |ringE| defined, |semantics1 ringE e| has type |Expr A → Expr A|.
Evaluating, for example |semantics1 ringE e (Ind :+ Lit 1)|, yields
\begin{spec}
  e' =  Lit 3 :× (Ind :+ Lit 1) :× (Ind :+ Lit 4) :+
          Lit 2 :× Ind :+ (Ind :+ Lit 1) {-"~~."-}
\end{spec}
Note that |Lit Ind| in |e| is replaced by the argument |Ind :+ Lit 1|.
Furthermore, one layer of |Lit| is removed, thus both |Lit 3| and |Ind :+ Lit 4|
is exposed to the outermost level. The expression |e'| may then be evaluated by
|semantics1 rngℕ|, yielding a natural number. In summary, the function
|semantics2| that evalulates |Expr (Expr A)| can be defined by:
\begin{spec}
semantics2 : ∀ {A} → Ring A → Expr (Expr A) → Expr A → A → A
semantics2 rng e2 e1 x = semantics1 rng (semantics1 ringE e2 e1) x {-"~~."-}
\end{spec}

This is how |Expr (Expr ℕ)| simulates bivariate polynomials: the two
indeterminates are respectively represented by |Ind| and |Lit Ind|. During
evaluation, |Ind| can be instantiated to an expression |arg| of type |Expr ℕ|, while |Lit Ind| can be instantiated to a |ℕ|. If |arg| contains |Ind|, it
refers to the next indeterminate.

What about subexpressions like |Lit (Ind :+ Lit 4)|? One can see that
its semantics is the same as |Lit Ind :+ Lit (Lit 4)|, the expression we get by
pushing |Lit| to the leaves. In general, define the following function:
\begin{spec}
litDist : ∀ {A} → Expr (Expr A) → Expr (Expr A)
litDist = foldE Ind (foldE (Lit Ind) (Lit ∘ Lit) ringE) ringE {-"~~."-}
\end{spec}
The function traverses through the given expression and, upon encountering
a subtree |Lit e|, lifts |e| to |Expr (Expr A)| while distributes |Lit| inwards
|e|. We can prove the following theorem:
\begin{theorem} For all |e : Expr (Expr A)| and |r : Ring A|, we have
|semantics2 r (litDist e) = semantics2 r e|.
\end{theorem}

What we have shown in this section echos a known result: the bivariate
polynomial ring $R[X,Y]$ is isomorphic to $R[X][Y]$, modulo |litDist|.

\subsection{Multivariate Polynomials}
In general, as we have mentioned in Section~\ref{sec:introduction}, the
multivariate polynomial $R[X_1,X_2\ldots,X_m]$ is isomorphic to
univariate polynomial ring $S[X_m]$ over the base ring
$S=R[X_1,X_2,\ldots,X_{m-1}]$ (modulo the distribution law of |Lit|).
That is, a polynomial over |A| with |n| indeterminates
can be represented by |ExprN n A|, where
\begin{spec}
ExprN zero     A = A
ExprN (suc n)  A = Expr (ExprN n A) {-"~~."-}
\end{spec}

To define the semantics of |ExprN n A|, recall that, among its |n| indeterminates,
the outermost indeterminate shall be instantiated to an expression of type
|ExprN (n-1) A|, the next indeterminate to |ExprN (n-2) A|..., and the inner most indeterminate to |A|, before yielding a value of type |A|. Define
\begin{spec}
Tele : Set -> ℕ -> Set
Tele A zero     = ⊤
Tele A (suc n)  = ExprNn A × Tele A n {-"~~,"-}
\end{spec}
that is, |Tele A n| is a list of |n| elements, with the first having type |ExprN (n-1) A|, the second |ExprN (n-2)|, and so on. The type is called |Tele| because it resembles
a ``telescope'' in dependent types: latter expressions may refer to variables mentioned earlier.

The semantics |ExprN n A| is a function |Tele A n -> A|, which can be defined
inductively as below:
\begin{spec}
semantics : ∀ {A} -> Num A -> (n : ℕ) -> ExprNn A -> Tele A n -> A
semantics r zero     x  tt        = x
semantics r (suc n)  e  (t , es)  = semantics r n (semantics1 (ringES r) e t) es {-"~~."-}
\end{spec}
Essentially, |semantics r n| is |n|-fold composition of |semantics1 (ringES r)|,
each interpreting one level of the given expression. The function
|ringES| delivers the |Ring (ExprN n A)| instance for all |n|:
\begin{spec}
ringES : ∀ {A} → Ring A → ∀ {n} → Ring (ExprN n A)
ringES r zero  = r
ringES r _     = ringE {-"~~."-}
\end{spec}

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

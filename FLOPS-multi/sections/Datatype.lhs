 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
 %%include Formatting.fmt

\section{Datatype}
\label{sec:datatype}


%
In this section, we shall elaborate on what we mean by
Equation~\ref{eq:datatype} in Section~\ref{sec:introduction}.
%
We start with the categorical style as outlined by Bird and de
Moor~\cite{DBLP:books/daglib/0096998} and consider the following
recursively defined datatype over a datatype $A$:
%
\[ expr R ::= ind \mid lit\ R \mid add\ (expr\ R,expr\ R) \mid mul\
  (expr\ R,expr\ R). \]
%
This declares $[ind,lit,add,mul]_R:F(R,expr\ R)\rightarrow expr\ R$ as
the initial algebra of the functor $F(R,\cdot)$, where
$F(A,B)=1+A+(B\times B)+(B\times B)$ as defined in
Equation~\ref{eq:datatype}.
%
The datatype $expr\ R$ is a tree having two kinds of leaf nodes,
$ind$ and $lit\ R$, representing the indeterminate $X$ itself and
constants from $R$, respectively.
%
Furthermore, there are two ways to join two such binary trees, i.e.,
$add$ and $mul$, representing the addition and multiplication
operations in $R[X]$, respectively.
%
Clearly, each instance of such binary tree corresponds to the syntax
tree of a univariate polynomial from $R[X]$.
%

%
Naturally, the categorical-style definition of the datatype $expr\ R$
gives catamorphisms via $\mi{fold}$,
i.e.,
\begin{equation} \label{eq:catamorphism}
  \cata{f_i,f_\ell,f_a,f_m} % =fold\ (f_i,f_\ell,f_a,f_m)
    : expr~R\rightarrow S, \end{equation} where $f_i : 1\rightarrow S$,
$f_\ell : R\rightarrow S$, $f_a : S\rightarrow S\rightarrow S$, and
$f_m : S\rightarrow S\rightarrow S$.
%
This allows us to derive various functions in an economical way.


In Agda, the datatype can be expressed by the following declaration:
\begin{spec}
data Expr (A : Set) : Set where
  Ind : Expr A
  Lit : A -> Expr A
  Add : Expr A -> Expr A -> Expr A
  Mul : Expr A -> Expr A -> Expr A {-"~~,"-}
\end{spec}
and the $\mi{fold}$ it induces can be given by:
\begin{spec}
foldE : ∀ {A B : Set} -> B -> (A -> B) -> Num B -> Expr A -> B
foldE x f num        Ind          = x
foldE x f num        (Lit y)      = f y
foldE x f ((+) , _)  (Add e1 e2)  = foldE x f e1 + foldE x f e2
foldE x f (_ , (*))  (Mul e1 e2)  = foldE x f e1 * foldE x f e2 {-"~~,"-}
\end{spec}
where is a pair of operators specifying what operators to replace |Add| and |Mul| with. Each instance of |Num B| defines how to perform addition and multiplication for |B|.

\paragraph{Evaluation} Assuming a base type |A| for which |Num A| is defined, consider evaluating an expression of type |Expr A|.

\begin{spec}
num→ : ∀ {A B : Set} → Num B → Num (A → B)
num→ ((+),(*)) = ( \f g x -> f x + g x,
                   \f g x -> f x * g x) {-"~~."-}
\end{spec}

\begin{spec}
semantics1 : ∀ {A} → Num A → Expr A → A → A
semantics1 num = foldExpr id const (num→ num)
\end{spec}

{\bf Old contents below}

For example, it is natural to define the semantics of a polynomial
$f\in R[X]$ as the corresponding \emph{polynomial function}
$\tilde f:R\rightarrow R$ that sends $x\in R$ to $f(x)\in R$.
%
In this case, we let $S=R\rightarrow R$ in
Equation~\ref{eq:catamorphism}:
\[ semantics = fold\ (id_R,const_R,+,\times), \] where
$+ : (R\rightarrow R)\rightarrow (R\rightarrow R)\rightarrow
(R\rightarrow R)$ sums two polynomial functions point-wise, and
similarly $\times$, multiplies point-wise.
%
From here, we can see that in general, it is nature to require the
datatype $S$ to behave like a ring in order to have a ``reasonably
natural'' catamorphism.
%

%
The situation for multivariate polynomials is similar but a bit more
complicated.
%
As we have mentioned in Section~\ref{sec:introduction}, we will
construct multivariate polynomials by identifying
$R[X_1,X_2\ldots,X_m]$ as a univariate polynomial ring $S[X_m]$ over
the base ring $S=R[X_1,X_2,\ldots,X_{m-1}]$.
%
Let us first consider the simplest multivariate polynomial ring,
namely, a bivariate polynomial ring $R[X,Y]\cong R[X][Y]$, which shall
be modeled using $expr\ (expr\ R)$.
%
Ideally, the semantics of a bivariate polynomial should be a (curried)
function of type $R\rightarrow R\rightarrow R$, i.e., the semantics
function should have the type
$expr\ (expr\ R)\rightarrow R\rightarrow R\rightarrow R$.
%
Now if we apply the $semantics$ function for univariate polynomials to
something of type $expr\ (expr\ R)$, we get something of type
$expr\ R\rightarrow expr\ R$.
%
Intuitively, this says that the ``semantics'' of $f(X,Y)\in R[X][Y]$
is a \emph{polynomial-valued} function
$f(X,\cdot) : R[X]\rightarrow R[X]$ that maps a polynomial
$g(X))\in R[X]$ to $f(X,g(X))\in R[X]$.
%
Then the semantics of $f(X,g(X))$ is of type $R\rightarrow R$,
suggesting that $semantics\circ (semantics\ f)$ may be a good starting
point for defining the semantics of a bivariate polynomial $f$.
%

%
Let us denote $expr\ (expr\ R)$ as $expr^2\ R$ and
$semantics\circ (semantics\ f)$ as $semantics_2\ f$.
%
Then from the above discussion, $semantics_2\ f$ is of type
$expr\ R\rightarrow R\rightarrow R$, which is strictly more than what
we want because $R$ is a proper subset of $expr\ R$.
%
Therefore, when we ``evaluate'' the semantics of a bivariate
polynomial $f\in R[X,Y]$ as a bivariate polynomial function (they
are!) at a point, we would need to ``lift'' one of the coordinates and
regard it as a univariate polynomial.
%
Another minor nuisance is that we would need to feed the arguments to
$semantics_2\ f$ in an order \emph{opposite} to the natural order.
%
That is, to evaluate the (ideal) semantics of a bivariate polynomial
$f(X,Y)\in R[X,Y]$, we would need to compute
$semantics_2\ f\ (lit\ y)\ x$.
%

%
In general, we can recursively define $semantics_{n+1}\ f$ as
\[ semantics\circ(semantics_n\ f) \] for $n\geq 1$.
%
Again we would need appropriate lifting and order reversing when
evaluating the semantics of a multivariate polynomial
$f(X_1,\ldots,X_n)\in R[X_1,\ldots,X_n]$ at a point
$(x_1,\ldots,x_n)\in R^n$ by computing
$semantics_n\ f\ (lit^{n-1}\ x_n)\ \cdots\ x_1$.
%

%
We can also define
$substitute : expr\ R\rightarrow expr\ R\rightarrow expr\ R$ in a
similar way using $fold$.
%
Intuitively, it should take two polynomials $f(X),g(X)\in R[X]$ and
substitute say $g(X)$ into $f(X)$ by replacing every occurence of $X$
in $f$ with $g(X)$.
%
If we ``inject'' $f(X)$ into $R[\_,X]$ and regard it as a bivariate
polynomial $f'(\_,X)$ in which the other indeterminate never occurs,
then the polynomial-valued function
$semantics\ f' : expr\ R\rightarrow expr\ R$ seems useful now.
%
That is, $semantics\ f'\ g$ would compute $f(g(X))$, which is
precisely what we want as $substitute\ f\ g$.
%
The only thing we need here is the ``injection'' function that, in
this case, injects univariate polynomials into a bivariate polynomial
ring.
%
Similar to $semantics$, we can also generalize $substitute$ to
$substitute_n : expr^n\ R\rightarrow\cdots\rightarrow expr^n R$ for
$n>1$ by appropriately injection and lifting.
%
Take $n=2$ as an example: to get $f(g_1(X,Y),g_2(X,Y))$ for
$f,g_1,g_2\in R[X,Y]$, we can compute
$substitute_2\ f\ g_1\ g_2=semantics_2\ f'\ g_2'\ g_1$, where
$f'\in R[\_,\_,X,Y]$ is the injection of $f$, and $g_2'=lit\ g_2$ is
the lifting of $g_2$ as discussed earlier in this section.
%

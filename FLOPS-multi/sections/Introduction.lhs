 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt

\section{Introduction}
\label{sec:introduction}

% It is a standard exercise in beginners' functional programming courses to
% define a datatype for arithmetic expressions:
% \begin{spec}
%   data Expr a = Lit a | Expr a :+ Expr a | Expr a :× Expr a {-"~~,"-}
% \end{spec}
% and define a function |Expr a -> a| to evaluate such expressions, provided that it is given
% how to perform addition and multiplication for type |a|. If we add an additional
% constructor denoting a variable, the data structure represents univariate polynomials. In this pearl, we will play around with types such as |Expr (Expr a)|, |Expr (Expr (Expr a))|... |ExprN n a|. We will claim that they are useful --- |ExprN n a| encodes a multivariate polynomial with |n| variables, and define various operations to manipulate them. Finally, we will show how such expressions can be compiled, inductively, to assembly programs that evaluates them, and prove the correctness of compilation.
%
% But let us motivate first.

A \emph{univariate polynomial} over a base ring $R$ is a finite sum of the form
\[ a_nX^n+a_{n-1}X^{n-1}+\cdots+a_0, \] where $a_i\in R$ are the
coefficients, and $X$ is called an \emph{indeterminate}.
%
The set of univariate polynomials over $R$ forms a ring, denoted as
$R[X]$.
%
We can allow two or more indeterminates $X_1,X_2,\ldots,X_m$ and thus
arrive at a \emph{multivariate polynomial}, a finite sum of the form
\[ \sum_{i}a_iX_1^{e_1^{(i)}}X_2^{e_2^{(i)}}\cdots X_m^{e_m^{(i)}}, \]
where $a_i\in R$ are coefficients, and $e_j^{(i)}$ are nonnegative
integers.
%
The set of $m$-variate polynomials over $R$, denoted as
$R[X_1,X_2,\ldots,X_m]$, also forms a ring, referred to as a
\emph{ring of polynomials}.
%

%
Polynomials are a central concept to many branches in mathematics and
computer science.
%
In particular, manipulation of polynomial expressions can be used to
model a wide variety of computation.
%
For example, every element of an algebraic extension field $F$ over a
base field $K$ can be identified as a polynomial over $K$, e.g.,
cf.~Theorem~1.6, Chapter~5 of the (standard) textbook by
Hungerford~\cite{hungerford2003algebra}.
%
Addition in $F$ is simply polynomial addition over $K$, whereas
multiplication in $F$ is polynomial multiplication modulo the defining
polynomial of $F$ over $K$.
%
Let us use the familiar case of the complex numbers over the real
numbers as a concrete example.
%
The complex numbers can be obtained by adjoining to the real numbers a
root $i$ of the polynomial $X^2+1$.
%
In this case, every complex number can be identified as a polynomial
$a+bi$ for $a,b$ real.
%
The addition of $a_1+b_1i$ and $a_2+b_2i$ is simply
$(a_1+a_2)+(b_1+b_2)i$, whereas the multiplication,
$(a_1+b_1i)(a_2+b_2i)\bmod i^2+1=(a_1a_2-b_1b_2)+(a_1b_2+a_2b_1)i$.
%

%
Such arithmetic in a (finite) field finds rich application in, e.g.,
elliptic curve cryptography~\cite{DBLP:conf/crypto/Miller85}.
%
There we use the group structure of elliptic curves over finite fields
to do cryptography, and the group laws are often given in polynomial
expressions over finite fields.
%
(One or two more examples here.)
%

This pearl is motivated by our research in cryptography. On the one hand,
we often have to deal with multivariate polynomials over complicated base rings.
Complex number is just one example (todo: what else?). On the other hand, for
efficiency, these expressions have to be compiled to assembly language,
which usually support only arithmetic operations that fit in one machine word.
The conversion from mathematical expressions to assembly is usually done by hand. We wish to automate this process in stages: represent multivariates in
terms of univariates, and convert univariates over compound base rings to
multiple univariates over simple values that are ready for compilation. And
we wish to formally prove each of the steps correct.

\paragraph{From Univariate to Multivariate} A key observation this pearl is
based on is that there is an isomorphism between multivariate polynomials
$R[X_1,X_2\ldots,X_m]$ and univariate polynomial ring $S[X_m]$ over the base ring $S=R[X_1,X_2,\ldots,X_{m-1}]$, cf.~Corollary~5.7, Chapter~3 of
Hungerford~\cite{hungerford2003algebra}. This allows us to define a datatype
for univariate polynomials, and reuse it inductively to define multivariate
polynomials. Operations such as evaluation, substitution, etc., of the latter
can also be defined inductively in terms of that of the former.

% %
% For example, we can characterize a datatype for multivariate
% polynomials in a categorical style as outlined by, e.g., Bird and de
% Moor~\cite{DBLP:books/daglib/0096998}.
% %
% That is, we can define a base bifunctor $F$ as
% \begin{equation} \label{eq:datatype} F(A,B)=1+A+(B\times B)+(B\times
%   B). \end{equation}
% %
% Then a datatype $TA$ for (univariate) polynomials over a base ring of
% type $A$ will be $TA=F(A,TA)$, and that for multivariate polynomials
% will be $T^mA=T(T^{m-1}A)=F(T^{m-1}A,T^mA)$.
% %
% Here $T$ is a type functor, so the datatype $TA$ represents
% polynomials over datatype $A$.
%

%
Finally, we can compile a polynomial expression into in a
sequence of arithmetic expressions in its base ring.
%
This is useful when, e.g., implementing elliptic curve cryptography on
a microprocessor, on which there is no native hardware support for
polynomial arithmetic.
%
Again using multiplication of two complex numbers as an example, we
would need a sequence of real arithmetic expressions for implementing
$c_1+c_2i=(a_1+b_1i)\times(a_2+b_2i)$:
%
\begin{enumerate}
  %
\item $t_1\leftarrow a_1\times a_2$;
  %
\item $t_2\leftarrow b_1\times b_2$;
  %
\item $t_3\leftarrow a_1\times b_2$;
  %
\item $t_4\leftarrow b_1\times a_2$;
  %
\item $c_1\leftarrow t_1-t_2$;
  %
\item $c_2\leftarrow t_3+t_4$.
  %
\end{enumerate}
%
Furthermore, we would like to be able to prove the correctness of such
compilations, especially when the expressions get more and more
complicated, e.g., in real-world cryptographic algorithms.
%

%
The rest of this paper is organized as follows.
%
(Paper organization goes here.)
%

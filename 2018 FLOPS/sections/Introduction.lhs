 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt

\section{Introduction}
\label{sec:introduction}

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

In addition to arithmetic in an algebraic extension field,
manipulation of polynomial expressions also finds rich application in
cryptography in particular.
%
A wide variety of cryptosystems can be implemented using polynomial
expressions over a finite field or $\mathbb Z/n\mathbb Z$, the ring of
integers modulo $n$.
%
In elliptic curve cryptography~\cite{DBLP:conf/crypto/Miller85}, for
example, we use the group structure of certain elliptic curves over
finite fields to do cryptography, and the group laws are often given
in polynomial expressions over finite fields.
%
Another example is certain classes of post-quantum cryptosystems,
i.e., those expected to survive large quantum computers' attack.
%
Among the most promising candidates, we have multivariate
cryptosystems~\cite{conf/pqcrypto/ChenCCCY08} and several particularly
efficient lattice-based
cryptosystems~\cite{DBLP:journals/iacr/LyubashevskyPR12,DBLP:conf/ccs/CrockettP16},
for which encryption and decryption operations can be carried out
using polynomial expressions over finite fields or
$\mathbb Z/n\mathbb Z$.
%

This pearl is initially motivated by our research in cryptography.
%
On the one hand, we often have to deal with multivariate polynomials
over various base rings, as exemplified above.
%
% Complex number is just one example (todo: what else?). On the other hand, for
% efficiency, these expressions have to be compiled to assembly language,
% which usually support only arithmetic operations that fit in one machine word.
% The conversion from mathematical expressions to assembly is usually done by hand. We wish to automate this process in stages: represent multivariates in
% terms of univariates, and convert univariates over compound base rings to
% multiple univariates over simple values that are ready for compilation. And
% we wish to formally prove each of the steps correct.
%
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
%
On the other hand, we also need to compile a polynomial expression
into in a sequence of arithmetic expressions over its base ring.
%
This is useful for, e.g., software implementation of cryptosystems on
microprocessors with no native hardware support for arithmetic
operations with polynomials or integers of cryptographic sizes, which
typically range from a few hundreds to a few thousands of bits.
%
Again using multiplication of two complex numbers as an example, we
would need a sequence of real arithmetic expressions for implementing
$c_1+c_2i=(a_1+b_1i)\times(a_2+b_2i)$:
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
\todo{An example matching the description here?}
%
It might be surprising that, with the advance of compiler technology
today, such programs are still mostly coded and optimized manually,
sometimes in assembly language, for maximal efficiency.
%
Naturally, we would like to automate this process as much as possible.
%
Furthermore, with such safety-critical application we would like to
have machine-verified proofs that the compilation and optimizations are
correct.

In attempting toward this goal, we have come up with this pearl.
%
It is not yet practical but, we think, is neat and worth writing about.
%
A key observation is that there is an
isomorphism between multivariate polynomial ring
$R[X_1,X_2\ldots,X_m]$ and univariate polynomial ring $S[X_m]$ over
the base ring $S=R[X_1,X_2,\ldots,X_{m-1}]$, cf.~Corollary~5.7,
Chapter~3 of Hungerford~\cite{hungerford2003algebra}.
%
This allows us to define a datatype |Poly| for univariate polynomials, and
reuse it inductively to define multivariate polynomials --- an |n|-variate
polynomial can be represented by |PolyN n| (|Poly| applied |n| times).
%
Most operations on the polynomials can defined either in terms of the {\em fold}
induced by |Poly|, or by induction on |n|, hence the title.

We explore the use of |PolyN n| and its various implications in depth in
Section~\ref{sec:expressions}.
%
Then in Section~\ref{sec:operations}, we present implementations of common polynomial operations such as evaluation, substitution, etc.
%
We pay special attention to an operation |expand| and prove its correctness,
since it is essential in compilation.
%
In Section~\ref{sec:compilation}, we show how to compile a polynomial into an assembly program. We present a simple compilation, also defined in terms of fold, prove its correctness, while leaving further optimization to future work.
%
The formulation in this pearl have been implemented in both Haskell and Agda~\cite{Norell:08:Towards}, the latter also used to verify our proofs. The code is available on line at \todo{URL}.
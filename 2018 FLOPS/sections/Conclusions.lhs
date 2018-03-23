%include agda.fmt
%include Formatting.fmt

\section{Conclusions and Related Work}
\label{sec:conclusions}

In dependently typed programming, a typical choice in implementing
multivariate polynomials is to represent de Bruin indices using |Fin n|, the type having exactly |n| members. This is done in, for example, the |RingSolver| in the Agda standard library~\cite{Danielsson:17:Ring}, among many.
%
The tagless-final representation~\cite{Carette:09:Finally} is another alternative.
%
In this paper, we have explored yet another alternative,
chosen to see how far we can go in exploiting the isomorphism between
$R[X_1,X_2\ldots,X_m]$ and univariate polynomial ring
$R[X_1,X_2,\ldots,X_{m-1}][X_m]$.
%
It turns out that we can go quite far --- we managed to represent multivariate
polynomials using univariate polynomials.
%
Various operations on them can be defined inductively.
%
In particular, we defined how a polynomial of vectors can be expanded
to a vector of polynomials, and how a polynomial can be
compiled to sequences of scalar-manipulating instructions like
assembly-language programs.
%
The correctness proofs of those operations also turn out to be
straightforward inductions, once we figure out how to precisely
express the correctness property.

We note that the current expansion formula is provided by the
programmer.
%
For example, in order to expand a complex polynomial expression into
two real ones, the programmer needs to provide (in a |RingVec|) the formula
$(a_1+b_1i)(a_2+b_2i)\bmod i^2+1=(a_1a_2-b_1b_2)+(a_1b_2+a_2b_1)i$.
%
We can see that the divisor polynomial of the modular relationship can
actually give rise to an equational type in which $i^2+1=0$, or any
pair of polynomials are considered ``equal'' if their difference is a
multiple of the polynomial $i^2+1$.
%
In the future, we would like to further automate the derivation of
this formula, so the programmer will only need to give us the
definition of the equational types under consideration. The |RingSolver|~\cite{Danielsson:17:Ring} manipulates equations into normal
forms to solve them, and the solution can be used in Agda programs by
reflection. It is interesting to explore whether a similar approach may
work for our purpose.


% This is our first step toward studying the interplay between type
% systems and cryptography.

\paragraph{Acknowledgements} The authors would like to thank the members of IFIP Working Group 2.1 for their valuable comments on the first presentation of this work.

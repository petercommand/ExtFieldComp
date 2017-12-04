%include agda.fmt
%include Formatting.fmt

\section{Conclusions}
\label{sec:conclusions}

In dependently typed programming, a typical choice in implementing
multivariate polynomials is to represent de Bruin indices using |Fin n|, the type having exactly |n| members.
%
The tagless-final representation~\cite{Carette:09:Finally} is another alternative.
%
In this paper, we have exploited an alternative representation.
%
Our representation was chosen to see how far we can go in exploiting the
isomorphism between $R[X_1,X_2\ldots,X_m]$ and univariate polynomial ring
$R[X_1,X_2,\ldots,X_{m-1}][X_m]$.
%
It turns out that we can go quite far --- we managed to represent multivariate
polynomials using univariate polynomials.
%
Various operations on them can be defined inductively.
%
In particular, we defined how a polynomial of vectors can be expanded
to a vector of polynomials, and how a polynomial operations can be
compiled to sequences of scalar-manipulating instructions like
assembly-language programs.
%
The correctness proofs of those operations also turn out to be
straightforward inductions, once we figure out how to precisely
express the correctness property.

% This is our first step toward studying the interplay between type
% systems and cryptography.

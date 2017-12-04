%include agda.fmt
%include Formatting.fmt

\section{Conclusions}
\label{sec:conclusions}

Multivariate polynomials can be represented in many ways.
%
In dependently typed programming, a typical choice is to represent de Bruin
indices using |Fin n|, the type having exactly |n| members.
%
The tagless-final representation~\cite{Carette:09:Finally} is another alternative.
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
In particular, we defined how a polynomial of vectors can be expanded to a
vector of polynomials, and how a polynomial can be compiled to an assembly
program.
%
The correctness proofs of those operations also turn out to be straight
forward inductions, once we figure out how to precisely express the correctness
property.

% This is our first step toward studying the interplay between type
% systems and cryptography.
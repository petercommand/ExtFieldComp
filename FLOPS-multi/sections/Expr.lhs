 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
 %%include Formatting.fmt

% This is just a sample file.
% filename and section name to be changed later.

\section{Multi-Variable Expressons}
\label{sec:expressions}

\begin{spec}
data Expr {l} (A : Set l) : Set l where
  Ind : Expr A
  Lit : (x : A) -> Expr A
  Add : (e1 : Expr A) -> (e2 : Expr A) -> Expr A
  Sub : (e1 : Expr A) -> (e2 : Expr A) -> Expr A
  Mul : (e1 : Expr A) -> (e2 : Expr A) -> Expr A
\end{spec}

\begin{spec}
ExprN : ∀ {l} (A : Set l) (n : ℕ) -> Set l
ExprN A zero = A
ExprN A (suc n) = Expr (ExprN A n)

Nest : Set -> ℕ -> Set
Nest A zero = ⊤
Nest A (suc n) = ExprN A n × Nest A n
\end{spec}

\documentclass{llncs}
%
%include lhs2TeX.fmt
%include agda.fmt
%include polycode.fmt
%include Formatting.fmt

\title{Extension Field -- What Title Should We Use?}
%\titlerunning{Abbreviated Title}
%\subtitle{If We Need Any}
\author{Ivar Ekeland\inst{1} \and Roger Temam\inst{2}}
\institute{<name of an institute> \and <name of the next institute> \and <name of the next institute>}

\usepackage{amsmath}
\usepackage{amsthm}
%\usepackage[utf8]{inputenc}

\input{Preamble}

\begin{document}
%
\maketitle          % for the preliminaries
%
%\pagestyle{headings}  % switches on printing of running heads
\begin{abstract}
Abstract here.
\end{abstract}


\section{Introduction}
\label{sec:introduction}

How to sell this paper?



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


\end{document}

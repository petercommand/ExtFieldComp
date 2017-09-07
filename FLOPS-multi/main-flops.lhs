\documentclass{llncs}

%include agda.fmt

\title{Extension Field -- What Title Should We Use?}
%\titlerunning{Abbreviated Title}
%\subtitle{If We Need Any}
\author{Ivar Ekeland\inst{1} \and Roger Temam\inst{2}}
\institute{<name of an institute> \and <name of the next institute> \and <name of the next institute>}

\let\proof\relax
\let\endproof\relax

\usepackage{amsmath,amsthm,xspace}

\input{Preamble}

\newcommand{\cata}[1]{\ensuremath{(\! [#1]\! )}\xspace}

\begin{document}
%
\maketitle          % for the preliminaries
%
%\pagestyle{headings}  % switches on printing of running heads
\begin{abstract}
  % 
  Polynomials are a central concept to many branches in mathematics
  and computer science.
  % 
  In particular, manipulation of polynomial expressions can be used to
  model a wide variety of computation.
  %
  In this paper, we consider a simple recursive construction of
  multivariate polynomials over a base ring such as the integers or a
  (finite) field.
  %
  We show that this construction allows easy implementation of
  polynomial operations such as arithmetic, evaluation, substitution,
  etc.
  %
  Furthermore, we can compile a polynomial expression into in a
  sequence of arithmetic expressions in the base ring and prove the
  correctness of this compilation in Agda.
  %
  As a demonstration, we show how to recursively compile polynomial
  expressions over a tower of finite fields into scalar expressions
  over the ground field.
  % 
  Such a technique is not only interesting in its own right but also
  finds plentiful application in research areas such as cryptography.
  % 
\end{abstract}

 \input{sections/Introduction}
 \input{sections/Datatype}
 \input{sections/Expr}

\bibliographystyle{abbrv}
\bibliography{dblp,local}

\end{document}

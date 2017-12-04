\documentclass{llncs}

%include agda.fmt
%include Formatting.fmt

\title{Functional Pearl:\\ Folding Polynomials of Polynomials}
%\titlerunning{Needing a More Catchy Name}
%\subtitle{If We Need Any}
\author{Chen-Mou Cheng\inst{1} \and
        Ruey-Lin Hsu\inst{2} \and
        Shin-Cheng Mu\inst{3}}
\institute{%
  National Taiwan University, Taiwan \and
  National Central University, Taiwan \and
  Academia Sinica, Taiwan}

\let\proof\relax
\let\endproof\relax

\usepackage{amsmath,amsthm,xspace}

\input{Preamble}
\input{macros}

\newcommand{\cata}[1]{\ensuremath{(\! [#1]\! )}\xspace}
\newcommand{\todo}[1]{\{{\bf todo}: #1\}}

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
  We show that this construction allows inductive implementation of
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
 \input{sections/Expr}
 \input{sections/Operations}
 \input{sections/Compilation}
 \input{sections/Conclusions}

\bibliographystyle{abbrv}
\bibliography{dblp,local}

\end{document}

\documentclass{article}

\usepackage{amsmath}
\usepackage{amsthm}

%include lhs2TeX.fmt
%include agda.fmt
 %%include forall.fmt
%include polycode.fmt

 %include Formatting.fmt

%let showproofs = True

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\begin{document}

%format sem0 = "\Varid{sem}_{0}"
%format sem1 = "\Varid{sem}_{1}"
%format en1 = "\Varid{e}_{1+n}"
%format en = "\Varid{e}_{n}"
%format ei = "\Varid{e}_{i}"
%format esi = "\Varid{es}_{i}"
%format esn = "\Varid{es}_{n}"
%format rn = "\Varid{r}_{n}"
%format ri = "\Varid{r}_{i}"
%format compile0 = "\Varid{compile}_{0}"
%format sem1 = "\Varid{sem}_{1}"

%format reg n = "\Varid{r}_{" n "}"

\paragraph{Definitions} Define the semantics:
\begin{spec}
sem0 : a -> a
sem0 = id {-"~~,"-}

sem1 : Expr a -> a -> a
sem1 = foldExpr id const {-"~~,"-}

sem : (n : ℕ) -> Expr n a -> Nest n a -> a
sem 0        tt   x          = x
sem (1 + n)  en1  (en , es)  = sem n (sem1 en1 en) es {-"~~,"-}
\end{spec}
and compilation:
\begin{spec}
compile0 v = alloc >>= \r -> return (v , [ rn := v]) {-"~~,"-}

compile : (n : ℕ) -> Vec Addr n -> Expr n a -> M (Addr × [Instr])
compile  0     []         v    = compile0 v
compile  (1+n) (rn ∷ rs)  en1  = foldExpr (pass rn) (compile n rs) en1 {-"~~."-}
\end{spec}
Assume also the following
\begin{spec}
run : Heap -> [Instr] -> [Heap] {-"~~."-}
\end{spec}

This is theorem we wish to prove. Given |h : Heap|,
\begin{spec}
(∀ n (h : Heap) (rs : Vec Addr n) (en : Expr n a) (esn : Nest n) :
  (∀ i : 0 ≤ i < n : h ! ri = sem i ei esi) =>
    let (rn , ins) = compile en rs
    in run ins h ! rn = sem n en esn) {-"~~,"-}
\end{spec}
where |ri| is the |i|th element in |rs| (counting from the right),
|ei| is the element in |esn| having type |Expr i a|, and
|esi| is the rest of the ``list'' of expressions.
\end{document}

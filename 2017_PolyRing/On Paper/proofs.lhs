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
compile0 v = alloc >>= \ r -> return (v , [ rn := v]) {-"~~,"-}

compile : (n : ℕ) -> Vec Addr n -> Expr n a -> M (Addr × [Instr])
compile  0        []         v    = compile0 v
compile  (1 + n)  (rn ∷ rs)  en1  = foldExpr (pass rn) (compile n rs) en1 {-"~~."-}
\end{spec}
Assume also the following function that executes a compiled program:
\begin{spec}
run : Heap -> [Instr] -> [Heap] {-"~~,"-}
\end{spec}
whose definition is omitted.

\begin{theorem} We have
\begin{spec}
(∀ n (h : Heap) (rs : Vec Addr n) (en : Expr n a) (esn : Nest n a) ->
  (∀ i : 0 ≤ i < n : h ! ri = sem i ei esi) ->
    let (rn , ins) = runState (compile n rs en) r
    in run ins h ! rn = sem n en esn) {-"~~,"-}
\end{spec}
where |ei| is the element in |esn| having type |Expr i a|,
|esi| is the rest of the ``list'' of expressions, and
|ri| is the |i|th element in |rs| (counting from the right),
and |r| is a ``safe'' initial state (that ensures generation of
addresses does not overlap with |rs|).
\end{theorem}
\begin{proof} Induction on |n| and on structure of |en|.

\noindent {\bf Case} |n := 0|. We have |en : a| and |runState (compile en rs) r =
(r , [r := en])|. Immediately,
\begin{spec}
   run [r := en] h ! r
=  en
=  sem0 en {-"~~."-}
\end{spec}

\noindent {\bf Note:} do we need to make |n := 1| a separate case?

\noindent {\bf Case} |n := 1 + n|. We pattern-match |rs := rn ∷ rs| and
|esn := (en , esn)|. We do a case analysis on |en1|.

\noindent {\bf Case} |en1 := Ind|. We have
\begin{spec}
   runState (compile (1 + n) (rn ∷ rs) Ind) r
=    {- definition of |compile| -}
   runState (foldExpr (pass rn) (compile n rs) Ind) r
=    {- definition of |foldExpr| -}
   runState (pass rn) r
=  (rn, []) {-"~~,"-}
\end{spec}
and therefore
\begin{spec}
   run [] h ! rn
=  h ! rn
=    {- assumption -}
   sem n en esn
=    {- definition of |sem1| -}
   sem n (sem1 Ind en) esn
=    {- definition of |sem| -}
   sem (1 + n) Ind (en , esn) {-"~~."-}
\end{spec}

%format en' = "\Varid{e''}_{n}"
%format rn' = "\Varid{r''}_{n}"

\noindent {\bf Case} |en1 := Lit en'|. We have
\begin{spec}
   runState (compile (1 + n) (rn ∷ rs) Lit en') r
=    {- definition of |compile| -}
   runState (foldExpr (pass rn) (compile n rs) (Lit en')) r
=    {- definition of |foldExpr| -}
   runState (compile n rs en') r
=    {- introduce |rn'| and |ins| -}
   (rn' , ins) {-"~~."-}
\end{spec}
Furthermore,
\begin{spec}
   run ins h ! rn'
=    {- induction -}
   sem n en' esn
     {- definition of |sem1| -}
   sem n (sem1 (Lit en') en) esn
=    {- definition of |sem| -}
   sem (1 + n) (Lit en') (en , esn) {-"~~."-}
\end{spec}

%format oplus = "{\oplus}"
%format d1 = "\Varid{d}_{1}"
%format d2 = "\Varid{d}_{2}"

\noindent {\bf Case} |en1 := d1 oplus d2|
where |oplus| is one of the
binary operators. We have

\begin{spec}
   runState (compile (1 + n) (rn ∷ rs) (d1 oplus d2)) r
=    {- definition of |compile| -}
   runState (foldExpr (pass rn) (compile n rs) (d1 oplus d2)) r
=    {- definition of |foldExpr| -}
   runState (  compile n rs d1 >>= \ (a1, is1) ->
               compile n rs d2 >>= \ (a2, is2) ->
               alloc >>= \ a0 ->
               return (a0, is1 ++ is2 ++ [ a0 := a1 oplus a2 ])) r
=    {- see below -}
   (a0, is1 ++ is2 ++ [ a0 := a1 oplus a2 ])) {-"~~,"-}
\end{spec}
where the free variables are given by
\begin{spec}
(a1, is1)  = runState (compile n rs d1) r   {-"~~,"-}
(a2, is2)  = runState (compile n rs d2) r'  {-"~~, \mbox{for some $\Varid{r}''$.}"-}
\end{spec}

When running the compiled program:
\begin{spec}
  run (is1 ++ is2 ++ [ a0 := a1 oplus a2 ]) h ! a0
=   {- property of |run| -}
  run [ a0 := a1 oplus a2 ] (run is2 (run is1 h)) ! a0
=   {- definition of |run| -}
  (run is2 (run is1 h) ! a1) oplus (run is2 (run is1 h) ! a2)
=   {- Hmm.... need a lemma here! -}
  (run is1 h ! a1) oplus (run is2 (run is1 h) ! a2)
=   {- induction -}
  sem (1 + n) d1 (en , esn) oplus sem (1 + n) d2 (en , esn)
=   {- definitions of |foldExpr| and |sem| -}
  sem (1 + n) (d1 oplus d2) (en , esn) {-"~~."-}
\end{spec}
\end{proof}

\end{document}

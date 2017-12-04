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

\title{Proofs Regarding Extension Fields}
\author{}
\date{}

\maketitle

%format sem0 = "\Varid{sem}_{0}"
%format sem1 = "\Varid{sem}_{1}"
%format en1 = "\Varid{e}_{1+n}"
%format en = "\Varid{e}_{n}"
%format ei = "\Varid{e}_{i}"
%format e0 = "\Varid{e}_{0}"
%format e1 = "\Varid{e}_{1}"
%format e2 = "\Varid{e}_{2}"
%format esi = "\Varid{es}_{i}"
%format esn = "\Varid{es}_{n}"
%format rn = "\Varid{r}_{n}"
%format ri = "\Varid{r}_{i}"
%format compile0 = "\Varid{compile}_{0}"
%format sem1 = "\Varid{sem}_{1}"

%format reg n = "\Varid{r}_{" n "}"

\subsection*{Semantics and Compilation}

\paragraph{Definitions} Define the semantics:
\begin{spec}
sem0 : a -> a
sem0 = id {-"~~,"-}

sem1 : Expr a -> a -> a
sem1 = foldExpr id const {-"~~,"-}

sem : (n : ℕ) -> Expr n a -> Nest n a -> a
sem 0        x    tt          = x
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
=  sem 0 en esn {-"~~."-}
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
%format oplusA = "{\oplus_{A}}"
%format oplusE = "{\oplus_{E}}"
%format oplus1 = "{\oplus_{1}}"
%format oplus2 = "{\oplus_{2}}"
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

\subsection*{Expansion}

The function |expand| converts an expression those literals are vectors (of length |n|) to a vector of |n| expressions, each having |n| variables. The definition is given below. The |foldExpr| would demand a dictionay |Num (Vec (ExprN A n) n|:
\begin{spec}
expand : ∀ {A} n → Expr (Vec A n) → Vec (ExprN A n) n
expand n = foldExpr (genInd n) (map (liftVal n)) {-"~~."-}
\end{spec}
The function |genInd| generates a vector of variables:
\begin{spec}
genInd : ∀ {A : Set} (n : ℕ) → Vec (ExprN A n) n
genInd zero           = []
genInd (suc zero)     = Ind ∷ []
genInd (suc (suc n))  = Ind ∷ (map Lit (genInd (suc n))) {-"~~."-}
\end{spec}
For example |genInd 3 = Ind ∷ Lit Ind ∷ Lit (Lit Ind) ∷ []|.
The function |liftVal| lifts a value to |ExprN A n| by applying |Lit|:
\begin{spec}
liftVal : ∀ {l}{A : Set l} n → A → ExprN A n
liftVal zero x     = x
liftVal (suc n) x  = Lit (liftVal n x) {-"~~."-}
\end{spec}
The function |toNest| converts a vector of |A| to |Nest A n|, using |liftVal|:
\begin{spec}
toNest : ∀ {A n} → Vec A n → Nest A n
toNest {zero}   _         = tt
toNest {suc n}  (x ∷ xs)  = liftVal n x , toNest xs {-"~~."-}
\end{spec}
Given a vector of length |3|, for example, the first element is lifted by
|liftVal 2|, the second by |liftVal 1|, and the third element remains having type |A|.

The goal is to prove that |expand| is correct with respect to |sem|. For that we need two lemmas. Firstly, the semantics of a lifted literal is nothing but itself:
\begin{lemma}\label{lma:sem-liftVal}
For all |n|, |x|, and |es : Nest A n|, we have |sem n (liftVal n x) es = x|.
\end{lemma}
\begin{proof} Induction on |n|.

\noindent{\bf Case} |n := zero|.
\begin{spec}
   sem zero (liftVal zero x) xs
=    {- definition of |sem| -}
   liftVal zero x
=    {- definition of |liftVal| -}
   x {-"~~."-}
\end{spec}

\noindent{\bf Case} |n := suc n|.
\begin{spec}
   sem (suc n) (liftVal (suc n) x) (en , es)
=    {- definitions of |sem| and |litVal| -}
   sem n (foldExpr id const (Lit (liftVal n x)) en) es
=    {- definition of |foldExpr| -}
   sem n (liftVal n x) es
=    {- induction -}
   x {-"~~."-}
\end{spec}
\end{proof}

Secondly, the semantics of a list of indeterminents is just the environment:
\begin{lemma} \label{lma:sem-genInd}
For all |n| and |xs : Vec A n|, we have
|map (\ e → sem n e (toNest xs)) (genInd n) = xs|.
\end{lemma}
\begin{proof} Induction on |xs|.

\noindent{\bf Case} |xs := []|.
\begin{spec}
   map (\ e → sem zero e (toNest [])) (genInd zero)
=    {- definitions -}
   map (\e → e) []
=  [] {-"~~."-}
\end{spec}

\noindent{\bf Case} |xs := x ∷ []|.
\begin{spec}
   map (\ e → sem 1 e (toNest (x ∷ []))) (genInd 1)
=    {- definitions -}
   map (\ e → sem 1 e (x  ∷ [])) (Ind ∷ [])
=    {- definition of |map| -}
   sem 0 (sem1 Ind (x , tt))  ∷ []
=    {- definition of |sem1| -}
   foldExpr id const Ind x ∷ []
=  x  {-"~~."-}
\end{spec}

\noindent{\bf Case} |xs := x ∷ y ∷ xs|.
\begin{spec}
   map (\ e → sem (2+n) e (toNest (x ∷ y ∷ xs))) (genInd (2+n))
=    {- definition of |genInd| -}
   map (\ e → sem (2+n) e (toNest (x ∷ y ∷ xs)))
     (Ind ∷ map Lit (genInd (suc n)))
=    {- definition of |map|, |map|-fusion -}
   sem (2+n) Ind (toNest (x ∷ y ∷ xs)) ∷
     map (\ e → sem (2+n) (Lit e) (toNest (x ∷ y ∷ xs))) (genInd (suc n)) {-"~~."-}
\end{spec}
Concentrate on the head of the vector:
\begin{spec}
   sem (2+n) Ind (toNest (x ∷ y ∷ xs))
=    {- definition of |sem| and |toNest| -}
   sem (suc n) (sem1 Ind (liftVal (suc n) x)) (toNest (y ∷ xs))
=    {- definition of |sem1| -}
   sem (suc n) (liftVal (suc n) x) (toNest (y ∷ xs))
=    {- by Lemma \ref{lma:sem-liftVal} -}
   x {-"~~."-}
\end{spec}
To simplify the tail, we focus on |sem (2+n) (Lit e) (toNest (x ∷ y ∷ xs))|:
\begin{spec}
   sem (2+n) (Lit e) (toNest (x ∷ y ∷ xs))
=     {- definition of |sem| and |toNest| -}
   sem (suc n) (sem1 (Lit e) (liftVal (suc n) x)) (toNest (y ∷ xs))
=     {- definition of |sem1| -}
   sem (suc n) e (toNest (y ∷ xs)) {-"~~."-}
\end{spec}
Thus the tail is
\begin{spec}
   map (\ e → sem (2+n) (Lit e) (toNest (x ∷ y ∷ xs))) (genInd (suc n))
=     {- calculation above -}
   map (\ e → sem (suc n) e (toNest (y ∷ xs))) (genInd (suc n))
=     {- induction -}
   y ∷ xs {-"~~."-}
\end{spec}
Therefore |map (\ e → sem (2 + n) e (toNest (x ∷ y ∷ xs))) (genInd (2 + n)) = x ∷ y ∷ xs|.
\end{proof}

This is the main theorem:
\begin{theorem} For all |n|, |e : Expr (Vec A n)|, and |xs : Vec A n|,
we have
\begin{spec}
  sem1 e xs = map (\ e → sem n e (toNest xs)) (expand n e) {-"~~,"-}
\end{spec}
if the dictionary used in |sem1| and that used in |expand| are generated
from the same generator that is polymorphic.
\end{theorem}
\begin{proof} Induction on structure of |e|. The two base cases makes direct use of the two lemmas we just proved.

\noindent {\bf Case} |e := Ind|
\begin{spec}
   map (\ e → sem n e (toNest xs)) (expand n Ind)
=    {- definition of |expand| -}
   map (\ e → sem n e (toNest xs)) (genInd n)
=    {- by Lemma \ref{lma:sem-genInd} -}
   xs
=    {- definition of |sem1| -}
   sem1 e xs {-"~~."-}
\end{spec}

\noindent {\bf Case} |e := Lit ys|
\begin{spec}
   map (\ e → sem n e (toNest xs)) (expand n (Lit ys))
=    {- definition of |expand| -}
   map (\ e → sem n e (toNest xs)) (map (liftVal n) ys)
=    {- |map|-fusion -}
   map (\ y → sem n (liftVal n y) (toNest xs)) ys
=    {- by Lemma \ref{lma:sem-liftVal} -}
   map (\ y → y) ys
=  ys
=    {- definition of |sem1| -}
   sem1 (Lit ys) xs {-"~~."-}
\end{spec}

\noindent {\bf Case} |e := e0 oplus e1| where |oplus| is a binary operator. In the computation of |sem1|, we need an operator that performs |oplus| for vectors of
type |Vec A n|. Denote this operator by |oplusA|. In the computation of |expand|, we need another operator that combines vectors of expressions (|Vec (ExprN A n) n|), which we will denote by |oplusE|.
\begin{spec}
   sem1 (e0 oplus e1) xs
=    {- definition of |sem1| -}
   sem1 e0 xs oplusA sem1 e1 xs
=    {- induction, abbreviating |(\ e → sem n e (toNest xs))| to |eval| -}
   map eval (expand n e0) oplusA map eval (expand n e1)
=    {- see below -}
   map eval (expand n e0 oplusE expand n e1))
=    {- definition of |expand| -}
   map (\ e → sem n e (toNest xs)) (expand n (e0 oplus e1)) {-"~~."-}
\end{spec}
The property we need in the penultimate step looks rather familiar.
In fact, it holds if |oplusA| and |oplusE| are both generated from the same
|lift| operator that lifts element-wise binary operators to vectors, and
|lift| is polymorphic.
That is, |oplusA = lift opA| and |oplusE = lift opE| for some
|opA : A → A → A| and |opE : ExprN A n → ExprN A n → ExprN A n|, where
|lift| has type:
\begin{spec}
  lift : ∀ {A} → (A → A → A) → {n} →
             Vec A n → Vec A n → Vec A n {-"~~."-}
\end{spec}
That |lift| being polymorphic means that it applies the given operator
to the two vectors merely by inspecting their shape, but not their contents.
The free theorem of |lift| is:
\begin{spec}
  ∀ {X Y : Set} →
    ∀  (f : X → Y) {n : ℕ}
       (op1 : X → X → X) (op2 : Y → Y → Y) →
    ∀ (xs ys : Vec X n) ->
       let (oplus1 , oplus2) = (lift op1, lift op2)
       in map f (xs oplus1 ys) = (map f xs) oplus2 (map f ys) {-"~~."-}
\end{spec}
The property we want follows from the free theorem by letting
|f := eval|, |xs := expand n e0|, and |ys := expand n e1|.
\begin{spec}
\end{spec}
\end{proof}
\end{document}

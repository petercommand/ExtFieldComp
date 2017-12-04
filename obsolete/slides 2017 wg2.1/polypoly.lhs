\documentclass[xcolor=dvipsnames,fleqn]{beamer}

\usetheme[outer/numbering=none]{metropolis}
%\usepackage{fontspec}
\usepackage{FiraSans}
\usepackage{FiraMono}
\metroset{titleformat=smallcaps}
\setsansfont[BoldFont={Fira Sans},ItalicFont={Fira Sans Light Italic}]{Fira Sans Light}

\usepackage{scalerel}

%include agda.fmt
 %%include forall.fmt
 %%include polycode.fmt
%include Formatting.fmt

\input{colortheme.tex}

\title{Fun with Polynomials of Polynomials}
\author{Chen-Mou Cheng \and Ruey-Lin Hsu \and Shin-Cheng Mu}
\date{Autumn, 2017}
%\institute{Academia Sinica}

\setbeamertemplate{footline}[frame number]

\begin{document}
\frame{\titlepage}

\frame{
\frametitle{The Standard ``Expression'' Exercise}

A standard exercise for beginners: define |eval : Expr a -> a|.
\begin{spec}
  data Expr a = Lit a | Expr a :+ Expr a | Expr a :× Expr a {-"~~,"-}
\end{spec}

With an additional constructor |Var| for variables, the semantics
becomes |Expr a -> a -> a|.

This talk: we have a use for |Expr (Expr (... a))|.
}

\frame{
\frametitle{Motivation}

|ExprN n a| simulates |n|-variate polynomials.

In cryptography we have to deal with multivariate polynomials
over complicated base rings.

These expressions have to be compiled to assembly language,
which usually support only arithmetic operations that fit in
one machine word.

Goal: convert a multivariate polynomial over aggregated base ring
to a collection of univariate polynomials over simple bring ring,
and compile them to assembly.

}

\frame{
\frametitle{Expressions}

\begin{spec}
data Expr (A : Set) : Set where
  Var   : Expr A
  Lit   : A -> Expr A
  (:+)  : Expr A -> Expr A -> Expr A
  (:×)  : Expr A -> Expr A -> Expr A {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Fold}

\begin{spec}
foldE : ∀ {A B : Set} -> B -> (A -> B) -> Ring B -> Expr A -> B
foldE x f rng        Var         = x
foldE x f rng        (Lit y)     = f y
foldE x f ((+),(×))  (e1 :+ e2)  =  foldE x f ((+),(×)) e1 +
                                    foldE x f ((+),(×)) e2
foldE x f ((+),(×))  (e1 :× e2)  =  foldE x f ((+),(×)) e1 ×
                                    foldE x f ((+),(×)) e2 {-"~~."-}
\end{spec}

\begin{spec}
Ring : Set -> Set
Ring A = (A -> A -> A) × (A -> A -> A) {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Evaluation}

\begin{spec}
ringFn : ∀ {A B : Set} → Ring B → Ring (A → B)
ringFn ((+),(×)) = (  \ f g x -> f x + g x,
                      \ f g x -> f x × g x) {-"~~."-}
\end{spec}

\begin{spec}
semantics1 : ∀ {A} → Ring A → Expr A → A → A
semantics1 rng = foldE id const (ringFn rng) {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Bivariate Polynomial}

Consider
\begin{spec}
e :  Expr (Expr ℕ)
e =  Lit (Lit 3) :× Var :× Lit (Var :+ Lit 4) :+ Lit Var :+ Var {-"~~."-}
\end{spec}

Evaluating |e|, letting the variable be |Var :+ Lit 1 : Expr ℕ|, yields:
\begin{spec}
e' :  Expr ℕ:
e' =  Lit 3 :× (Var :+ Lit 1) :× (Var :+ Lit 4) :+ Var :+ (Var :+ Lit 1) {-"~~."-}
\end{spec}
which can be further evaluated given a |ℕ|.

Therefore, |ExprN 2 ℕ| simulates a bivariate polynomial.
}

\frame{
\frametitle{Evaluating a Bivaraite Polynomial}

\begin{spec}
semantics2 : ∀ {A} → Ring A → ExprN 2 A → Expr A → A → A
semantics2 rng e2 e1 x =
  semantics1 rng (semantics1 ((:+), (:×)) e2 e1) x {-"~~."-}
\end{spec}

\begin{spec}
ringE : ∀ {A} → Ring (Expr A)
ringE = ((:+), (:×)) {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Bivaraite Polynomial}

|ExprN 2 ℕ| simulates bivariate polynomials: the two
indeterminates are respectively |Var| and |Lit Var|.

|Var| can be instantiated to an expression |arg| of type |Expr ℕ|,
while |Lit Var| can be instantiated to a |ℕ|. If |arg| contains |Var|, it
refers to the next indeterminate.

What about |Lit (Var :+ Lit 4)|? One can see that
its semantics is the same as |Lit Var :+ Lit (Lit 4)|.
}

%format semantics3 = "\Varid{eval}_{3}"
%format semantics4 = "\Varid{eval}_{4}"

\frame{
\frametitle{More Variables?}

\begin{spec}
semantics2  : Ring A -> Expr2 A
            -> Expr A -> A -> A
semantics2 rng e = semantics1 rng . semantics1 ((:+), (:×)) e
\end{spec}
\begin{spec}
semantics3  : Ring A -> ExprN 3 A
            -> Expr2 A -> Expr A -> A -> A
semantics3 rng e = semantics2 rng . semantics1 ((:+), (:×)) e
\end{spec}
\begin{spec}
semantics4  : Ring A -> ExprN 4 A
            -> ExprN 3 A -> Expr2 A -> Expr A -> A -> A
semantics4 rng e = semantics3 rng . semantics1 ((:+), (:×)) e
\end{spec}
}

\frame{
\frametitle{Evaluating Multivariate Polynomials}

|Tele A n| expands to |ExprN (n-1) A × ExprN (n-2) A × .. × A × ⊤|.
\begin{spec}
Tele : Set -> ℕ -> Set
Tele A zero     = ⊤
Tele A (suc n)  = ExprNn A × Tele A n {-"~~,"-}
\end{spec}

Evaluating |ExprNn A|:
\begin{spec}
semantics  : ∀ {A} -> Ring A
           -> (n : ℕ) -> ExprNn A -> Tele A n -> A
semantics r zero     x  tt        = x
semantics r (suc n)  e  (t , es)  =
  semantics r n (semantics1 (ringES r) e t) es {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Rotation}

Swapping the two outermost indeterminates of an
|Expr2 A|, using |foldE|.
\begin{spec}
rotaExpr2 : ∀ {A} → Expr2 A → Expr2 A
rotaExpr2 = foldE (Lit Var) (foldE Var (Lit ∘ Lit) ringE) ringE
  where ringE = ((:+), (:×)) {-"~~."-}
\end{spec}

}

\frame{
\frametitle{More Rotations}

Rotating the first 3 variables:
\begin{spec}
rotaExpr3 : ∀ {A} → ExprN 3 A → ExprN 3 A
rotaExpr3 = fmap rotaExpr2 ∘ rotaExpr2 {-"~~,"-}
\end{spec}

and the first 3 variables:
\begin{spec}
rotaExpr4 : ∀ {A} → ExprN 4 A → ExprN 4 A
rotaExpr4 = fmap (fmap rotaExpr2) . rotaExpr3 {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Rotation in General}

\begin{spec}
rotaExprN : ∀ {A} (n : ℕ) → ExprNn A → ExprNn A
rotaExprN zero                 = id
rotaExprN (suc zero)           = id
rotaExprN (suc (suc zero))     = rotaExpr2
rotaExprN (suc (suc (suc n)))  =
    (fmapN (suc n)) rotaExpr2 . rotaExprN  (suc (suc n)) {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Substitution}

Given an expression |e|, substitute, for each occurrence of |Var|,
another expression |e'|.

Recalling that the type of |semantics1| can be instantiated to
|ExprN 2 A → Expr A → Expr A|.

Lift |e| to |ExprN 2 A|, do a |rotaExpr2| to
expose the |Var| inside |e|, and use |semantics1|:
\begin{spec}
substitute1 : ∀ {A} → Expr A → Expr A → Expr A
substitute1 e e' = semantics1 ((:+), (:×)) (rotaExpr2 (Lit e)) e' {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Substituting Two Variables}

What about |e : Expr2 A|? Lift it to an |ExprN 4 A|, perform two
|rotaExpr4| to expose its two indeterminates, before using |semantics2|:
\begin{spec}
substitute2 :: ∀ {A} → Expr2 A -> Expr2 A -> Expr2 A -> Expr2 A
substitute2 e e' e'' =
  semantics2 ((:+), (:×))
     (rotaExpr4 . rotaExpr4 $ Lit (Lit e)) (Lit e') e'' {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Expansion}

The polynomial over complex numbers $(3 + 2i) x^2 + (2 + i)x + 1$
can be represented by |Expr (Real × Real)|, with semantics
|(Real × Real) -> (Real × Real)|.

Let $x$ be $x_1 + x_2 i$, the
polynomial can be expanded as below:
\begin{align*}
  & (3 + 2i)(x_1 + x_2 i)^2 + (2 + i)(x_1 + x_2 i) + 1 \\
% =~& (3 x^2_1 - 4 x_1 x_2 - 3 x^2_2) + \\
%   & (2 x^2_1 + 6 x_1 x_2 - 2 x^2_2) i +\\
%   & (2 x_1 - x_2) + (x_1 + 2 x_2) i + 1\\
=~& (3 x^2_1 + 2 x_1 - 4 x_1 x_2 - x_2 - 3 x^2_2 + 1) +\\
  & (2 x^2_1 + x_1 + 6 x_1 x_2 + 2 x_2 - 2x^2_2) i \mbox{~~.}
\end{align*}
That is, |Expr (Real × Real)| can be expanded to
|(Expr2 Real × Expr2 Real)|.

The expansion, certainly, depends on how we define addition
and multiplication for complex numbers.
}

%format WordN = "\Varid{Word}^{\Varid{n}}"

\frame{
\frametitle{Why the Expansion?}

It might turn out that |Real| is represented by a fixed
length of machine words, |Real = WordN|, and |Expr WordN| can be further
expanded to $|(ExprN n Word)|^\Varid{n}$, this time using arithmetic
operations defined for |Word|.

Now that each polynomial is defined
over |Word|, whose arithmetic operation is supported by the machine, we may
compile the expressions to assembly.
}

\frame{
\frametitle{Expansion in General}

In general, a univariate polynomial of |n|-vectors, |Expr (Vec A n)|, can be
expanded to a |n|-vector of |n|-variate polynomial, |Vec (ExprN n A) n|.

}
\frame{
\frametitle{Helper functions and Definitions}
%format LitN1 = "\Varid{Lit}^{\Varid{n-1}}"
\begin{itemize}
\item |genVars n = Var ∷ Lit Var ∷ ... LitN1 Var ∷ []|.
\item |liftVal : ∀ {A} n → A → ExprNn A| lifts |A| to |ExprNn A| by applying
|Lit| to it |n| times.
\item Define a type for functions that lifts arithmetic operators
for |A| to that for |Vec A n|:
\begin{spec}
RingVec : Set1
RingVec = ∀ {A} n -> Ring A -> Ring (Vec A n) {-"~~."-}
\end{spec}
\end{itemize}
}

\frame{
\frametitle{Expansion in General}

Expansion can now be defined by:
\begin{spec}
expand : ∀ {A} n → RingVec → Expr (Vec A n) → Vec (ExprN n A) n
expand ringVec n =
    foldE (genVars n) (map (liftVal n)) (ringVec ((:+), (:×))) {-"~~."-}
\end{spec}

The real work is all done in |ringVec ((:+), (:×))|.
}

\frame{
\frametitle{Correctness of Expansion}

\begin{theorem} For all |n|, |e : Expr (Vec A n)|, |xs : Vec A n|,
|r : Ring A|, and |ringVec : RingVec|, we have
\begin{spec}
  semantics1 (ringVec r) e xs =
    map (\ e -> semantics r n e (toTele xs)) (expand ringVec n e) {-"~~,"-}
\end{spec}
if |ringVec| is polymorphic.
\end{theorem}
}

%format +. = "\mathbin{+_{A}}"
%format +.. = "\mathbin{+_{E}}"

\frame{
\frametitle{Why Polymorphism?}

At one point of the proof, the property unfolds to:
\begin{spec}
  semantics1 e1 xs +. semantics1 e2 xs =
    map (λ e → semantics n e xs')
            (expand n e1 +.. expand n e2)
\end{spec}
where |xs' = toTele xs|, and |(+.)| and |(+..)| are respectively
addition for vectors of |A|, and vectors of expressions.

If |(+.) = ringVec r| and |(+..) = ringVec ((:+), (:×))|, the property
is guaranteed by free theorem of |ringVec|.
}

\frame{
\frametitle{Compilation: Instructions}

\begin{spec}
data TAC (A : Set) : Set where
  ConstI  : Addr → A → TAC A
  AddI    : Addr → Addr → Addr → TAC A
  MulI    : Addr → Addr → Addr → TAC A {-"~~,"-}

Ins A = List (TAC A){-"~~."-}
\end{spec}
}

%format compile0 = "\Varid{compile}_{0}"

\frame{
\frametitle{Compilation}

Compiling |ExprN 0 A|, that is, |A|:
\begin{spec}
compile0 : ∀ {A} → A → M (Addr × Ins A)
compile0 v =  alloc >>= \ addr →
              return (addr , ConstI addr v ∷ []){-"~~,"-}
\end{spec}
where |M| is a state monad keeping track of addresses allocated, etc.
}

\frame{
\frametitle{Compilation}
Compiling |ExprNn A|, assuming that values of the |n|
variables are stored in a given vector of addresses:
\begin{spec}
compile :  ∀ {A} n → Vec Addr n
           → ExprNn A → M (Addr × Ins A)
compile zero     addr        e = compile0 e
compile (suc n)  (x ∷ addr)  e =
  foldE (pass x) (compile n addr) (add, mul) e {-"~~,"-}
 where  pass r = return (r , [])
        add m1 m2 =  m1 >>= \ (a1, ins1) ->
                     m2 >>= \ (a2, ins2) ->
                     alloc >>= \ addr → return
                     (addr, ins1 ++ ins2 ++ [AddI a1 a2 addr])  {-"~~."-}
\end{spec}
}

\frame{
\frametitle{Running A Program}

\begin{spec}
runIns : ∀ {A} → Ring A → Heap A → Ins A → Heap A
\end{spec}
Definition omitted.
}

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

\frame{
\frametitle{Correctness of Compilation}

\begin{theorem}
\begin{spec}
(∀ n (h : Heap) (rs : Vec Addr n) (en : Expr n a) (esn : Tele n a) ->
  (∀ i : 0 <= i < n : h ! ri = semantics i ei esi) ->
    let (rn , ins) = runState (compile n rs en) r
    in run ins h ! rn = semantics n en esn) {-"~~, where"-}
\end{spec}
\vspace{-1cm}
\begin{itemize}
\item |ei| is the element in |esn| having type |Expr i a|,
\item |esi| is the rest of the vector of expressions, and
\item |ri| is the |i|th element in |rs|,
\item and |r| is a ``safe'' initial state (that ensures generation of
addresses does not overlap with |rs|).
\end{itemize}
\end{theorem}
}
\end{document}

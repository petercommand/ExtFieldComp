 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Operations on Polynomials}
\label{sec:operations}

Having defined a representation for multivariate polynomials, we ought to
demonstrate that this representation is feasible --- that we can define most of
the operations we want. In this section we show ...

\subsection{Rotation}

The first operation we consider swaps the two outermost indeterminates of an
|Expr2 A|, using |foldE|. It is perhaps instructive comparing it with
|litDist|.
\begin{spec}
rotaExpr2 : ∀ {A} → Expr2 A → Expr2 A
rotaExpr2 = foldE (Lit Ind) (foldE Ind (Lit ∘ Lit) ringE) ringE {-"~~."-}
\end{spec}
In |rotaExpr2|, the outermost |Ind| is replaced by |Lit Ind|. When
encountering |Lit e|, the inner |e| is lifted to |Expr2 A|. The |Ind| inside
|e| remains |Ind|, which becomes the outermost indeterminate after lifting.
Note that both |litDist| and |rotaExpr2| apply to |ExprN n A| for all |n ≥ 2|,
since |A| can be instantiated to an expression as well.

Consider |ExprN 3 A|, a polynomial with (at least) three indeterminates. To
"rotate" the three indeterminates, that is, turn |Lit Ind| to |Ind|, |Lit (Lit Ind)| to |Lit Ind|, and |Ind| to |LitN 3 Ind|, we could do:
\begin{spec}
  rotaExpr3 = fmap rotaExpr2 ∘ rotaExpr2 {-"~~,"-}
\end{spec}
where |fmap| is the usual ``map'' function:
\begin{spec}
  fmap : ∀ {A B} -> (A -> B) -> Expr A -> Expr B {-"~~."-}
\end{spec}
The first |rotaExpr2| swaps the two outer indeterminates, while |fmap rotaExpr2|
swaps the inner two. To rotate the outermost four indeterminates of an |ExprN 4 A|, we may define:
\begin{spec}
rotaExpr4 = fmap (fmap rotaExpr2) . rotaExpr3 {-"~~."-}
\end{spec}
In general, the following function rotates the first |n| indeterminates of
the given polynomial:%
\begin{spec}
rotaExprN : ∀ {A} (n : ℕ) → ExprNn A → ExprNn A
rotaExprN zero                 = id
rotaExprN (suc zero)           = id
rotaExprN (suc (suc zero))     = rotaExpr2
rotaExprN (suc (suc (suc n)))  = (fmapN (suc n)) rotaExpr2 . rotaExprN  (suc (suc n)) {-"~~."-}
\end{spec}
Note that in the actual Agda code we need to convince Agda that
|ExprN n (Expr A)| is the same type as |Expr (ExprN n A)| and use |subst|
to do type conversion. We omit the details here for clarity.

Given |m| and |n|, |rotaExprNm n m| compose |rotaExprN n| with itself
|m| times. Therefore, the first |n| indeterminates are rotated |m| times.
It will be handy in the next section.
\begin{spec}
rotaExprNm : ∀ {A} (n m : ℕ) → ExprNn A → ExprNn A
rotaExprNm n zero e = e
rotaExprNm n (suc m) e = rotaExprNm n m (rotaExprN n e) {-"~~."-}
\end{spec}

\subsection{Substitution}

%format substitute1 = "\Varid{substitute}_{1}"
%format substitute2 = "\Varid{substitute}_{2}"

Substitution is another operation one would expect. Given an expression |e|,
how do we substitute, for each occurrence of |Ind|, another expression |e'|,
using operations we have defined? Recalling that the type of
|semantics1| can be instantiated to |ExprN 2 A → Expr A → Expr A|, we may
lift |e| to |ExprN 2 A| by wrapping it with |Lit|, do a |rotaExpr2| to
expose the |Ind| inside |e|, and use |semantics1| to perform the
substitution:
\begin{spec}
substitute1 : ∀ {A} → Expr A → Expr A → Expr A
substitute1 e e' = semantics1 ringE (rotaExpr2 (Lit e)) e' {-"~~."-}
\end{spec}
What about |e : Expr2 A|? We may lift it to an |ExprN 4 A|, perform two
|rotaExpr4| to expose its two indeterminates, before using |semantics2|:
\begin{spec}
substitute2 :: ∀ {A} → Expr2 A -> Expr2 A -> Expr2 A -> Expr2 A
substitute2 e e' e'' =
  semantics2 ringE (rotaExpr4 . rotaExpr4 $ Lit (Lit e)) (Lit e') e'' {-"~~."-}
\end{spec}

We now consider the general case with |e : ExprN n A| and a vector of |n|
expressions, each of type |ExprN n A|.
(to do: can be simplified) 
\begin{spec}
substitute : ∀ {A} n -> ExprNn A -> Vec (ExprN n A) n -> ExprNn A
substitute zero e e' = e
substitute {A} (suc n) e e'
   = semantics {ExprN A (suc n)} {{toExprNumN {A} (suc n)}} (suc n)
        (subst id (sym (ExprN-comb {A} (suc n) (suc n)))
          (rotaExprN-m (suc n + suc n) (suc n)
             (liftExpr {_} {_} {suc n} {suc n + suc n}
               (≤→≤′ (suc n) (suc (n + suc n)) (s≤s (≤-weakening n n (suc n) ≤-refl))) e)))
        (prodReplicate→Nest (suc n) e')
\end{spec}

\subsection{Expansion}

expansion

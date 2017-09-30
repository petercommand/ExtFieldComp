 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Operations on Polynomials}
\label{sec:operations}

To be elaborated later:

rotation

\begin{spec}
rotaExpr2 : ∀ {A : Set} {{num : Num A}} → Expr2 A → Expr2 A
rotaExpr2 = foldExpr {{toExprNumN 2}} (Lit Ind)
              (foldExpr {{toExprNumN 2}} Ind (Lit ∘ Lit))

rotaExprN : ∀ {A : Set} {{num : Num A}} (n : ℕ) → ExprN A n → ExprN A n
rotaExprN zero = id
rotaExprN (suc zero) = id
rotaExprN (suc (suc zero)) = rotaExpr2
rotaExprN (suc (suc (suc n))) = subst (\ x → Expr (Expr x) → Expr (Expr x)) (numEquiv _ n)
                                      (fmapN {_} {1} (suc n) rotaExpr2 ∘ rotaExprN {{toExprNumN 1}} (suc (suc n)))

rotaExprN-m : ∀ {A : Set} {{num : Num A}} (n m : ℕ) → ExprN A n → ExprN A n
rotaExprN-m n zero e = e
rotaExprN-m n (suc m) e = rotaExprN-m n m (rotaExprN n e)
\end{spec}

substitution

\begin{spec}
substitute : ∀ {A : Set}{{num : Num A}} (n : ℕ) -> ExprN A n -> prodReplicate (ExprN A n) n -> ExprN A n
substitute zero e e' = e
substitute {A} (suc n) e e'
   = semantics {ExprN A (suc n)} {{toExprNumN {A} (suc n)}} (suc n)
        (subst id (sym (ExprN-comb {A} (suc n) (suc n)))
          (rotaExprN-m (suc n + suc n) (suc n)
             (liftExpr {_} {_} {suc n} {suc n + suc n}
               (≤→≤′ (suc n) (suc (n + suc n)) (s≤s (≤-weakening n n (suc n) ≤-refl))) e)))
        (prodReplicate→Nest (suc n) e')
\end{spec}

expansion

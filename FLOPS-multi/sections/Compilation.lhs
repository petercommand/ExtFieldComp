 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Compiling Polynominal}
\label{sec:compilation}

\begin{spec}
Addr : Set
Addr = ℕ

data TAC (A : Set) : Set where
  ConstI : Addr → A → TAC A
  AddI   : Addr → Addr → Addr → TAC A
  MulI   : Addr → Addr → Addr → TAC A
\end{spec}

\begin{spec}
compile0 : ∀ {A} → A → SSA (Addr × Ins A)
compile0 v =  alloc >>= \ addr →
              return (addr , ConstI addr v ∷ [])

compile :  ∀ {A} n → Vec Addr n
           → ExprNn A → SSA (Addr × Ins A)
compile zero     addr        e = compile0 e
compile (suc n)  (x ∷ addr)  e = foldE (pass x) (compile n addr) e
\end{spec}

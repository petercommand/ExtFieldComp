 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Compiling Polynominal}
\label{sec:compilation}

We finally to compilation (some more intro.).

We consider a simple imaginary machine with a heap that may abstractly be seen as a function |Addr -> A|: each cell stores a value of type |A| and can be referred to by |Addr|. The assembly language we consider consists of three instructions:
\begin{spec}
data TAC (A : Set) : Set where
  Const : Addr → A → TAC A
  Add   : Addr → Addr → Addr → TAC A
  Mul   : Addr → Addr → Addr → TAC A {-"~~,"-}

Ins : Set -> Set
Ins A = List (TAC A) {-"~~."-}
\end{spec}
The interpretation is simple: the command |Const i v| stores value |v| in address |i|, |Add i j k| fetches values stored in addresses |i| and |j| and stores their sum in address |k|, and similarly with |Mul|.

(something brief about executing a program)

To compile a program we employ a monad |SSA|
\begin{spec}
compile0 : ∀ {A} → A → SSA (Addr × Ins A)
compile0 v =  alloc >>= \ addr →
              return (addr , ConstI addr v ∷ [])

compile :  ∀ {A} n → Vec Addr n
           → PolyNn A → SSA (Addr × Ins A)
compile zero     addr        e = compile0 e
compile (suc n)  (x ∷ addr)  e = foldE (pass x) (compile n addr) e
\end{spec}

\paragraph{Correctness}

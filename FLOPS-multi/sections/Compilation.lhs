 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Compiling Polynominal}
\label{sec:compilation}

We finally come to compilation (some more intro.).

We consider a simple imaginary machine with a heap, denoted by |Heap A| that may abstractly be seen as a function |Addr -> A|: each cell in the heap stores a value of type |A| and can be referred to by |Addr|. The assembly language we consider consists of three instructions:
\begin{spec}
data TAC (A : Set) : Set where
  Const : Addr → A → TAC A
  Add   : Addr → Addr → Addr → TAC A
  Mul   : Addr → Addr → Addr → TAC A {-"~~,"-}

Ins : Set -> Set
Ins A = List (TAC A) {-"~~."-}
\end{spec}
The interpretation is simple: the command |Const i v| stores value |v| in address |i|, |Add i j k| fetches values stored in addresses |i| and |j| and stores their sum in address |k|, and similarly with |Mul|. Given arithmetic operators for |A| and a heap, executing an assembly program computes a new heap:
\begin{spec}
runIns : ∀ {A} → Ring A → Heap A → Ins A → Heap A {-"~~."-}
\end{spec}

To compile a program we employ a monad |SSA|, which support an operation |alloc : SSA Addr| that returns the address of an unused cell in the heap. The monad can be implemented by, for example, a state monad that keeps a counter of the highest address that is allocated. Compilation of a polynomial yields |SSA (Addr × Ins A)|, where the second component of the pair is an assembly program, and the first component is the address where the program, once run, stores the value of the polynomial. We define of |PolyN n A| by induction on |n|. For the base case |PolyN 0 A = A|, we simply allocate a new cell and stores the given value there using |Const|:
\begin{spec}
compile0 : ∀ {A} → A → SSA (Addr × Ins A)
compile0 v =  alloc >>= \ addr →
              return (addr , Const addr v ∷ []) {-"~~."-}
\end{spec}
For the inductive case,
\begin{spec}
compile :  ∀ {A} n → Vec Addr n
           → PolyNn A → SSA (Addr × Ins A)
compile zero     addr        e = compile0 e
compile (suc n)  (x ∷ addr)  e = foldE (pass x) (compile n addr) e {-"~~."-}
\end{spec}

\paragraph{Correctness}

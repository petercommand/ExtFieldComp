 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Compiling Polynominal}
\label{sec:compilation}

We finally come to compilation (some more intro.).

We consider a simple imaginary machine with a heap, denoted by |Heap| that may abstractly be seen as mapping between memory addresses |Addr| and machine words |Word|. The operator |(!!) : Heap -> Addr -> Word| fetches the value stored in the given address, while |ringWord : Ring Word| defines how words are added and multiplied. The simple assembly language we consider consists of three instructions:
\begin{spec}
data TAC : Set where
  Const : Addr → Word → TAC
  Add   : Addr → Addr → Addr → TAC
  Mul   : Addr → Addr → Addr → TAC {-"~~,"-}

Ins : Set
Ins = List TAC {-"~~."-}
\end{spec}
The command |Const i v| stores value |v| in address |i|, |Add i j k| fetches values stored in addresses |i| and |j| and stores their sum in address |k|, and similarly with |Mul|. Given a heap, executing an assembly program computes a new heap:
\begin{spec}
runIns : Heap → Ins → Heap {-"~~."-}
\end{spec}

To compile a program we employ a monad |SSA|, which support an operation |alloc : SSA Addr| that returns the address of an unused cell in the heap. As a naive approach, |SSA| can be implemented by a state monad that keeps a counter of the highest address that is allocated. Compilation of a polynomial yields |SSA (Addr × Ins)|, where the second component of the pair is an assembly program, and the first component is the address where the program, once run, stores the value of the polynomial. We define compilation of |PolyN n Word| by induction on |n|. For the base case |PolyN 0 Word = Word|, we simply allocate a new cell and stores the given value there using |Const|:
\begin{spec}
compile0 : Word → SSA (Addr × Ins)
compile0 v =  alloc >>= \ addr →
              return (addr , Const addr v ∷ []) {-"~~."-}
\end{spec}
To compile a polynomial of type |PolyNn Word|, we assume that the value of the |n|
indeterminants are already computed and stored in the heap, the locations of which are stored in a vector of |n| addresses. The function |compile| takes a vector
\begin{spec}
compile :  ∀ n → Vec Addr n
           → PolyNn Word → SSA (Addr × Ins)
compile zero     addr        e = compile0 e
compile (suc n)  (x ∷ addr)  e =
    foldE (return (x, [])) (compile n addr) ringSSA e {-"~~,"-}
\end{spec}
In the clause for |suc n|, |x| is the address storing the value for the outermost indeterminant. To compile |Ind|, we simply return this address without generating any code. To compile |Lit e| where |e : PolyNn Word|, we inductively call |compile n addr|. The generated code is combined by |ringSSA|, defined by
\begin{spec}
ringSSA : Ring (SSA (Addr × Ins A))
ringSSA = (biOp Add, biOp Mul) {-"~~,"-}
\end{spec}
where |biOp op p1 p2| runs |p1| and |p2| to obtain the compiled code, allocate
a new address |dest|, before generating a new instruction |op dest addr1 addr2|:
\begin{spec}
biOp  : (Addr → Addr → Addr → TAC)
      → SSA (Addr × Ins) → SSA (Addr × Ins)
      → SSA (Addr × Ins)
biOp op m1 m2 =  m1 >>= \ (addr1 , ins1) →
                 m2 >>= \ (addr2 , ins2) →
                 alloc >>= \ dest →
                 return (dest , ins1 ++ ins2 ++ (op dest addr1 addr2 ∷ [])) {-"~~."-}
\end{spec}

\paragraph{Correctness}
Intuitively, if a polynomial |e| is compiled to a program |ins|, the compilation
is correct of |ins| computes the value which |e| would be evaluated to. A formal statement of correctness is complicated by the fact that |e : PolyNn A| expects, as arguments, |n| polynomials arranged as a descending chain, and |ins| expects their values to be stored in the heap.

Given a heap |h|, a chain |es : DChain Word n|, and a vector of addresses |rs|,
the predicate |Consistent h es rs| holds if the values of each polynomial in |es| is stored in |h| at the corresponding address in |rs|.
%
The predicate can be expressed by the following |Agda| datatype:
\begin{spec}
data  Consistent (h : Heap) : ∀ {n} → DChain Word n → Vec Addr n → Set where
  []   :  Consistent h tt []
  (∷)  :  ∀ {n : ℕ} {es rs e r}
          → (h !! r ≡ semantics n ringWord e es)
          → Consistent h       es        rs
          → Consistent h (e ,  es) (r ∷  rs)
\end{spec}

\begin{spec}
comp-sem : ∀ {A : Set} {{_ : Num A}} (n : ℕ)
  → (e : ExprN A n)
  → (es : Nest A n)
  → {h : Heap A}
  → (rs : Vec Addr n) → (r₀ : Addr)
  → HeapCons h es rs
  → All (\ e → r₀ > e) n rs
  → runCompile rs r₀ e h ≡ semantics n e es

runCompile : ∀ {A : Set} {{_ : Num A}} {n : ℕ}
             → Vec Addr n → Addr → ExprN A n → Heap A → A
runCompile {n = n} rs r₀ e h =
     runSSA {n = n} (compile n rs e) r₀ h

--

runSSA : ∀ {A : Set} {{_ : Num A}} {n : ℕ}
       → SSA (Addr × Ins A) → Addr → Heap A → A
runSSA (ssa m) r₀ h =
  let ((r , ins) , _) = m r₀
  in getHeap r (runIns h ins)
\end{spec}

 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Compiling Polynominal}
\label{sec:compilation}

We finally come to compilation (some more intro.).

We consider a simple imaginary machine with a heap, denoted by |Heap A| that may abstractly be seen as a function |Addr -> A|: each cell in the heap stores a value of type |A| and can be referred to by |Addr|. The simple assembly language we consider consists of three instructions:
\begin{spec}
data TAC (A : Set) : Set where
  Const : Addr → A → TAC A
  Add   : Addr → Addr → Addr → TAC A
  Mul   : Addr → Addr → Addr → TAC A {-"~~,"-}

Ins : Set -> Set
Ins A = List (TAC A) {-"~~."-}
\end{spec}
The command |Const i v| stores value |v| in address |i|, |Add i j k| fetches values stored in addresses |i| and |j| and stores their sum in address |k|, and similarly with |Mul|. Given arithmetic operators for |A| and a heap, executing an assembly program computes a new heap:
\begin{spec}
runIns : ∀ {A} → Ring A → Heap A → Ins A → Heap A {-"~~."-}
\end{spec}

To compile a program we employ a monad |SSA|, which support an operation |alloc : SSA Addr| that returns the address of an unused cell in the heap. As a naive approach, |SSA| can be implemented by a state monad that keeps a counter of the highest address that is allocated. Compilation of a polynomial yields |SSA (Addr × Ins A)|, where the second component of the pair is an assembly program, and the first component is the address where the program, once run, stores the value of the polynomial. We define compilation of |PolyN n A| by induction on |n|. For the base case |PolyN 0 A = A|, we simply allocate a new cell and stores the given value there using |Const|:
\begin{spec}
compile0 : ∀ {A} → A → SSA (Addr × Ins A)
compile0 v =  alloc >>= \ addr →
              return (addr , Const addr v ∷ []) {-"~~."-}
\end{spec}
To compile a polynomial of type |PolyNn A|, we assume that the value of the |n|
indeterminants are already computed and stored in the heap, the locations of which are stored in a vector of |n| addresses. The function |compile| takes a vector
\begin{spec}
compile :  ∀ {A} n → Vec Addr n
           → PolyNn A → SSA (Addr × Ins A)
compile zero     addr        e = compile0 e
compile (suc n)  (x ∷ addr)  e =
    foldE (return (x, [])) (compile n addr) ringSSA e {-"~~,"-}
\end{spec}
In the clause for |suc n|, |x| is the address storing the value for the outermost indeterminant. To compile |Ind|, we simply return this address without generating any code. To compile |Lit e| where |e : PolyNn A|, we inductively call |compile n addr|. The generated code is combined by |ringSSA|, defined by
\begin{spec}
ringSSA : Ring (SSA (Addr × Ins A))
ringSSA = (biOp Add, biOp Mul) {-"~~,"-}
\end{spec}
where |biOp op p1 p2| runs |p1| and |p2| to obtain the compiled code, allocate
a new address |dest|, before generating a new instruction |op dest addr1 addr2|:
\begin{spec}
biOp : ∀ {A}  → (Addr → Addr → Addr → TAC A)
              → SSA (Addr × Ins A) → SSA (Addr × Ins A)
              → SSA (Addr × Ins A)
biOp op m1 m2 =  m1 >>= \ (addr1 , ins1) →
                 m2 >>= \ (addr2 , ins2) →
                 alloc >>= \ dest →
                 return (dest , ins1 ++ ins2 ++ (op dest addr1 addr2 ∷ [])) {-"~~."-}
\end{spec}

\paragraph{Correctness}
Intuitively, if a polynomial |e| is compiled to a program |ins|, the compilation
is correct of |ins| computes the value which |e| would be evaluated to. A formal statement of correctness is complicated by the fact that |e : PolyNn A| expects, as arguments, |n| polynomials arranged as a telescope, and |ins| expects their values to be stored in the heap.

Given a heap |h|, a telescope |es : Tele A n|, and a vector of addresses |rs|,
the predicate |Consistent h es rs| holds if the values of each polynomial in the telescope |es| is stored in |h| at the corresponding address in |rs|. The predicate can be expressed by the following |Agda| datatype:
\begin{spec}
data  Consistent {A} (h : Heap A) :
      ∀ {n} → Tele A n → Vec Addr n → Set where
  []   :  Consistent h tt []
  (∷)  :  ∀ {n : ℕ} {es rs e r}
          → ((rng : Ring A) → getHeap r h ≡ semantics n rng e es)
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

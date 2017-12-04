 %%include lhs2TeX.fmt
%include agda.fmt
 %%include polycode.fmt
%include Formatting.fmt


\section{Compiling Polynominal}
\label{sec:compilation}

We finally come to compilation of potentially complicated polynomial
expressions.
%
As we have seen in Section~\ref{sec:introduction} and the previous
section, such compilation is useful for software implementation of
cryptosystems on microprocessors with no native hardware support for
the underlying arithmetic operations.
%
Furthermore, even for hardware implementation, such compilation can be
useful, as we can break down a complicated polynomial expression into
a sequence of simpler arithmetic operations in a smaller algebraic
structure, reducing the design complexity.

We consider a simple imaginary machine with a heap, denoted by |Heap|
that may abstractly be seen as mapping between memory addresses |Addr|
and machine words |Word|.
%
Albeit its simplicity, we believe that such a model captures the
essential aspects of a wide variety of hardware and software
implementations.
%
The operator |(!!) : Heap -> Addr -> Word| fetches the value stored in the given address, while |ringWord : Ring Word| defines how words are added and multiplied. The simple assembly language we consider consists of three instructions:
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

To compile a program we employ a monad |SSA|, which support an operation |alloc : SSA Addr| that returns the address of an unused cell in the heap.
%
As a naive approach, |SSA| can be implemented by a state monad that keeps a counter of the highest address that is allocated, while |alloc| returns the current value of the counter before incrementing it.
%
To run a |SSA| monad we use a function |runSSA : ∀ {A St} → St →
SSA St A → (A × St)| that takes a state |St| and yields a pair with the
result and the new state.

Compilation of a polynomial yields |SSA (Addr × Ins)|, where the second component of the pair is an assembly program, and the first component is the address where the program, once run, stores the value of the polynomial.
%
We define compilation of |PolyN n Word| by induction on |n|. For the base case |PolyN 0 Word = Word|, we simply allocate a new cell and stores the given value there using |Const|:
\begin{spec}
compile0 : Word → SSA (Addr × Ins)
compile0 v =  alloc >>= \ addr →
              return (addr , Const addr v ∷ []) {-"~~."-}
\end{spec}
To compile a polynomial of type |PolyNn Word|, we assume that the value of the |n|
indeterminants are already computed and stored in the heap, the locations of which are stored in a vector of |n| addresses.
\begin{spec}
compile :  ∀ n → Vec Addr n → PolyNn Word → SSA (Addr × Ins)
compile zero     addr        e = compile0 e
compile (suc n)  (x ∷ addr)  e =
    foldP (return (x, [])) (compile n addr) ringSSA e {-"~~,"-}
\end{spec}
In the clause for |suc n|, |x| is the address storing the value for the outermost indeterminant. To compile |Ind|, we simply return this address without generating any code. To compile |Lit e| where |e : PolyNn Word|, we inductively call |compile n addr|. The generated code is combined by |ringSSA|, defined by
\begin{spec}
ringSSA : Ring (SSA (Addr × Ins))
ringSSA = (biOp Add, biOp Mul) {-"~~,"-}
\end{spec}
where |biOp op p1 p2| runs |p1| and |p2| to obtain the compiled code, allocate
a new address |dest|, before generating a new instruction |op dest addr1 addr2|:
\begin{spec}
biOp  : (Addr → Addr → Addr → TAC)
      → SSA (Addr × Ins) → SSA (Addr × Ins) → SSA (Addr × Ins)
biOp op m1 m2 =  m1 >>= \ (addr1 , ins1) →
                 m2 >>= \ (addr2 , ins2) →
                 alloc >>= \ dest →
                 return (dest , ins1 ++ ins2 ++ (op dest addr1 addr2 ∷ [])) {-"~~."-}
\end{spec}

The following function compiles a polynomial, runs the program, and retrieves the resulting value from the heap:
\begin{spec}
compileRun : ∀ {A : Set} {n : ℕ}
             → Vec Addr n → Addr → PolyN A n → Heap A → A
compileRun rs r₀ e h =
    let  ((r , ins) , _) = runSSA r₀ (compile _ rs e)
    in   runIns h ins !! r {-"~~."-}
\end{spec}

\paragraph{Correctness} Given a polynomial |e|, by correctness of compilation we intuitively mean that the compiled program computes the value which |e| would be evaluated to.
%
A formal statement of correctness is complicated by the fact that |e : PolyNn A| expects, as arguments, |n| polynomials arranged as a descending chain, each of them expects arguments as well, and |ins| expects their values to be stored in the heap.

Given a heap |h|, a chain |es : DChain Word n|, and a vector of addresses |rs|, the predicate |Consistent h es rs| holds if the values of each polynomial in |es| is stored in |h| at the corresponding address in |rs|.
%
The predicate can be expressed by the following |Agda| datatype:
\begin{spec}
data  Consistent (h : Heap) :
      ∀ {n} → DChain Word n → Vec Addr n → Set where
  []   :  Consistent h tt []
  (∷)  :  ∀ {n : ℕ} {es rs e r}
          → (h !! r ≡ sem n ringWord e es)
          → Consistent h       es        rs
          → Consistent h (e ,  es) (r ∷  rs) {-"~~."-}
\end{spec}
Observe that in the definition of |(∷)| the descending chain |es| is supplied to each invocation of |sem| to compute value of |e|, before |e| itself is accumulated to |es|.

The correctness of |compile| can be stated as:
%All (\ e → r₀ > e) n rs
\begin{spec}
compSem : ∀ (n : ℕ) {h : Heap}
  → (e : PolyNn Word)
  → (es : DChain Word n)
  → (rs : Vec Addr n) → (r₀ : Addr)
  → Consistent h es rs
  → NoOverlap r₀ rs
  → compileRun rs r₀ e h ≡ sem n e es {-"~~."-}
\end{spec}
The predicate |Consistent h es rs| states that the values of the descending chain |es| are stored in the corresponding addresses |rs|.
%
The predicate |NoOverlap r₀ rs| states that, if an |SSA| monad is run with starting address |r₀|, all subsequent allocated addresses will not overlap with those in |rs|.
%
With the naive counter-based implementation of |SSA|, |NoOverlap r₀ rs| holds if |r₀| is larger than every element in |rs|.
%
The last line states that the polynomial |e| is compiled with argument addresses |es| and starting address |r₀|, and the value the program computes should be the same as the semantics of |e|, given the descending chain |es| as arguments.

With all the setting up, the property |compSem n e| can be proved by induction on |n| and |e|.

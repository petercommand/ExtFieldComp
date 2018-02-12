module Tests.Compile where

open import Data.Vec
open import Data.Product
open import Data.Integer
import Data.List
import Data.Nat

open import Tests.Instance
open import PolyRing
open import Compile

open Integer

postulate
  heap : Heap ℤ


-- Use the compile function to compile our target expression to SSA
-- If you are using agda-mode in emacs, use C-c C-n compileTest1 RET to see the result SSA
compileTest1 : SSA (Addr × Ins ℤ)
compileTest1 = compile 1 (0 ∷ []) (Add (Lit (ℤ.pos 5)) Ind)


-- After compiling our target expression, we apply the function runSSA with a big enough r₀ (ensuring that it does not clash with the elements in the Heap) (in this case, bigger than 0 will suffice) to get the final result
runCompileTest1 : ℤ
runCompileTest1 = runSSA compileTest1 10 (putHeap 0 (ℤ.pos 13) heap)



compileTest2 : SSA (Addr × Ins ℤ)
compileTest2 = compile 2 (1 ∷ 0 ∷ []) (Add (Lit Ind) (Mul Ind (Lit (Lit (ℤ.negsuc 7)))))


runCompileTest2 : ℤ
runCompileTest2 = runSSA compileTest2 10 (putHeap 0 (ℤ.pos 3) (putHeap 1 (ℤ.negsuc 12) heap))

import tmp.sheaf.xif.paper.S1823BCProductsActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Finite

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

-- the exact target, restated with Mathlib's functor (no reference to S1823.bc)
example (K : Type) [Field K] :
    PreservesFiniteProducts (CommAlgCat.FiniteEtale.baseChange.{0, 0, 0} K (AlgebraicClosure K)) :=
  S1823.bc_preservesFiniteProducts K

-- the recorded Prop of S1769/S1794
example (K : Type) [Field K] : S1823.BCPreservesFiniteProducts K :=
  S1823.bcPreservesFiniteProducts K

-- the general field extension version
example (K L : Type) [Field K] [Field L] [Algebra K L] :
    PreservesFiniteProducts (CommAlgCat.FiniteEtale.baseChange.{0, 0, 0} K L) :=
  S1823.bcOf_preservesFiniteProducts

#print axioms S1823.piFanIsLimit
#print axioms S1823.piRight_comp_eval
#print axioms S1823.bcOf_piFan_isLimit
#print axioms S1823.bcOf_preservesFiniteProducts
#print axioms S1823.bc_preservesFiniteProducts
#print axioms S1823.bcPreservesFiniteProducts
#print axioms S1823.bcPreservesFiniteProducts'

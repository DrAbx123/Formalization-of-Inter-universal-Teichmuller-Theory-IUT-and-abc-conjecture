/-
S1823 integration check: the S1769/S1794 third missing field is discharged by
S1823.bc_preservesFiniteProducts, and the S1769 reduction then gives field 3 of the
fibre functor (preservesFiniteCoproducts).
-/
import tmp.sheaf.xif.paper.S1823BCProductsActual
import tmp.sheaf.xif.paper.S1769FiberFunctorFieldsActual

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1823Check

/-- The exact condition of S1769 (its own definition, no unfolding by hand). -/
theorem s1769_condition (K : Type) [Field K] : S1769.BCPreservesFiniteProducts K :=
  S1823.bc_preservesFiniteProducts K

/-- Field 3 of the fibre functor of S1769, from S1769's reduction plus S1823. -/
theorem s1769_field3 (K : Type) [Field K] [PreGaloisCategory (S1769.C K)] :
    PreservesFiniteCoproducts (S1769.F K) :=
  S1769.preservesFiniteCoproducts_of K (S1823.bc_preservesFiniteProducts K)

#print axioms s1769_condition
#print axioms s1769_field3

end S1823Check

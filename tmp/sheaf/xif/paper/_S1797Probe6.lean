import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Epi
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped TensorProduct
namespace S1797Probe
variable {K : Type} [Field K]

#print axioms Algebra.isEpi_iff_forall_one_tmul_eq
#print axioms Algebra.isEpi_iff_surjective_algebraMap_of_finite
#print axioms Algebra.Etale.of_restrictScalars
#print axioms Algebra.Etale.comp
#print axioms Algebra.Etale.baseChange
#print axioms Module.Finite.of_restrictScalars_finite
#print axioms Module.Finite.trans
#print axioms Module.Finite.base_change
#print axioms Algebra.TensorProduct.includeLeft
#print axioms Algebra.TensorProduct.includeRight
#print axioms AlgHom.restrictScalars
#print axioms TensorProduct.smul_tmul
#print axioms IsScalarTower.of_algebraMap_eq
#print axioms RingHom.injective
#print axioms Algebra.Etale.iff_exists_algEquiv_prod
#print axioms Algebra.FormallyEtale.of_isSeparable
#print axioms Algebra.FinitePresentation.of_finiteType
#print axioms LinearMap.injective_iff_surjective_of_finrank_eq_finrank
#print axioms AlgHom.fst_prod
#print axioms AlgEquiv.ofBijective

end S1797Probe

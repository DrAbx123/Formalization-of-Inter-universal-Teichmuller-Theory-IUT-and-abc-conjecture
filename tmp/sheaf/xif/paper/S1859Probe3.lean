
import tmp.sheaf.xif.paper.S1858GlobalTraceActual
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section
open scoped TensorProduct
open LinearMap

namespace Probe3

variable {R M A : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A]

#check Algebra.lmul
#check Algebra.lmul_apply
#check Algebra.lmul_mul
#check LinearMap.comp_smul
#check LinearMap.smul_comp
#check LinearMap.add_comp
#check LinearMap.comp_add
#check Module.End.mul_eq_comp
#check LinearMap.trace_mul_comm
#check LinearMap.trace_comp_comm'
#check LinearMap.trace_comp_comm
#check LinearMap.trace_smul
#check LinearMap.map_smul
#check Module.Finite.exists_comp_eq_id_of_projective
#check Algebra.TensorProduct.instFree
#check Module.Finite.base_change
#check Module.Finite.tensorProduct
#check LinearMap.baseChange_comp
#check LinearMap.baseChange_id
#check LinearMap.baseChange_tmul
#check Algebra.baseChange_lmul
#check LinearMap.trace_baseChange
#check Module.Flat.projective_of_finitePresentation
#check Module.Projective.of_split
#check Module.free_of_flat_of_isLocalRing
#check Algebra.traceForm_apply
#check Algebra.trace_apply
#check LinearMap.BilinForm
#check LinearMap.mk₂
#check LinearMap.compr₂
#check LinearMap.BilinForm.mk₂
#check Algebra.TensorProduct.tmul_mul_tmul
#check LinearMap.trace_comp_comm'
end Probe3

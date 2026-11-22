import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange

noncomputable section
open scoped TensorProduct
open Module

namespace S1909TraceProbe

variable {R K V : Type*} [CommRing R] [Field K] [AddCommGroup V] [Module K V]
  [Algebra R K] [Module.Finite K V]

#check (inferInstance : Algebra R (Module.End K V))
#check (inferInstance : Algebra K (Module.End K V))
#check @LinearMap.trace_baseChange
#check @Module.End.trace_eq_sum_roots_charpoly_of_splits
#check @minpoly_dvd_charpoly
#check @IsIntegral.sum
#check @isIntegral_algHom_iff
#check @IsAlgClosed.splits
#check @AlgebraicClosure
#check @LinearMap.baseChange
#check @Polynomial.aeval
#check @Polynomial.aeval_map_algebraMap

end S1909TraceProbe

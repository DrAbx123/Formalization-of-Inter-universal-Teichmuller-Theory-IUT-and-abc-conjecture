import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange

noncomputable section
open scoped TensorProduct
open Module

namespace S1909TraceProbe

variable {R K A V : Type*} [CommRing R] [Field K] [CommRing A] [Algebra R K]
  [Algebra K A] [AddCommGroup V] [Module K V] [Module.Finite K V]

local instance : Algebra R (Module.End K V) :=
  (RingHom.toAlgebra' ((algebraMap K (Module.End K V)).comp (algebraMap R K)) (by
    intro c x
    ext v
    simp [Module.End.mul_apply, Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]))

example (y : A) (hy : IsIntegral R y) : IsIntegral R (Algebra.lmul K A y) := by
  exact IsIntegral.map (Algebra.lmul K A) hy

#check @IsIntegral.map

end S1909TraceProbe

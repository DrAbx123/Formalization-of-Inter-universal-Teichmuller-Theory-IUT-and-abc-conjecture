import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.PID

/-! GAP-step: change of basis determinant is a unit (GL_d). -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BasisDetUnitActual
open Module
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
/-- The determinant of the change-of-basis from `b` to `b'` is a unit of `R`. -/
theorem basis_change_det_isUnit (b b' : Module.Basis ι R M) :
    IsUnit (b.det b') :=
  b.isUnit_det b'
end LeanFormal.IUT.XiFPaper.Mzk1BasisDetUnitActual
end
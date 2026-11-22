import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.PID

/-! GAP-step: explicit change-of-basis matrix and its unit determinant. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ChangeMatrixActual
open Module
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Fintype ι] [DecidableEq ι]
/-- The change-of-basis matrix from `b` to `b'`. -/
noncomputable def changeMatrix (b b' : Module.Basis ι R M) : Matrix ι ι R :=
  b.toMatrix b'
/-- The determinant of the change-of-basis matrix is a unit. -/
theorem changeMatrix_det_isUnit (b b' : Module.Basis ι R M) :
    IsUnit (changeMatrix b b').det := by
  rw [changeMatrix, ← Basis.det_apply]
  exact b.isUnit_det b'
end LeanFormal.IUT.XiFPaper.Mzk1ChangeMatrixActual
end
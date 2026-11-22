import Mathlib

/-!
# Mzk1DetScalingInvLawsActual — determinant scaling and inverse laws (genuine Mathlib proofs)

Status: PENDING-VERIFY. No sorry, no axiom.
Genuine Mathlib determinant laws: det(c • A) = c^(card n) * det A and det(A⁻¹) = (det A)⁻¹
for matrices over ℚ. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DetScalingInvLawsActual

open Matrix

/-- Genuine determinant scaling law. -/
theorem det_smul_scaling {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℚ) (A : Matrix n n ℚ) :
    (c • A).det = c ^ Fintype.card n * A.det :=
  Matrix.det_smul c A

/-- Genuine determinant inverse law. -/
theorem det_inv_law {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℚ) :
    A⁻¹.det = (A.det)⁻¹ :=
  Matrix.det_inv A

end LeanFormal.IUT.XiFPaper.Mzk1DetScalingInvLawsActual

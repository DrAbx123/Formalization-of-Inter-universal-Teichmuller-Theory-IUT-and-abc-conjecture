import Mathlib

/-!
# Mzk1DetTransposeMulChainActual — chained determinant transpose consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers combining determinant multiplicativity with transpose invariance. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DetTransposeMulChainActual

open Matrix

/-- Chained: det of transpose product. -/
theorem det_transpose_mul_chain {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℚ) :
    (Aᵀ * Bᵀ).det = A.det * B.det := by
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose]

/-- Chained: determinant equals determinant of transpose. -/
theorem det_transpose_self_chain {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) : Aᵀ.det = A.det :=
  Matrix.det_transpose A

end LeanFormal.IUT.XiFPaper.Mzk1DetTransposeMulChainActual

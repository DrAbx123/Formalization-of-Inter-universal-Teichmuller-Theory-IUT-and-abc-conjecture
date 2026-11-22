import Mathlib

/-!
# Mzk1DetChainedConsumerActual — chained determinant consumer theorems (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers combining existing Mathlib determinant theorems into new conclusions. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DetChainedConsumerActual

open Matrix

/-- Chained: determinant of a scalar multiple of a product. -/
theorem det_smul_mul {n : Type*} [Fintype n] [DecidableEq n] (c : ℚ)
    (A B : Matrix n n ℚ) :
    (c • (A * B)).det = c ^ Fintype.card n * (A.det * B.det) := by
  rw [Matrix.det_smul, Matrix.det_mul]

/-- Chained: determinant of a product power. -/
theorem det_pow_mul {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℚ) (k : ℕ) :
    ((A * B) ^ k).det = (A.det * B.det) ^ k := by
  rw [Matrix.det_pow, Matrix.det_mul]

end LeanFormal.IUT.XiFPaper.Mzk1DetChainedConsumerActual

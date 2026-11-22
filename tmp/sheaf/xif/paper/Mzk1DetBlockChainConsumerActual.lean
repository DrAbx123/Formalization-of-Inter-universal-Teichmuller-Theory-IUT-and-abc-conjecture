import Mathlib

/-!
# Mzk1DetBlockChainConsumerActual — chained determinant block consumers (genuine)

Status: PENDING-VERIFY. No sorry, no axiom.
Chained consumers on determinants of matrix products (combining Mathlib det_mul/det_one). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DetBlockChainConsumerActual

open Matrix

/-- Chained: det of a three-fold product. -/
theorem det_mul_assoc_chain {n : Type*} [Fintype n] [DecidableEq n]
    (A B C : Matrix n n ℚ) :
    ((A * B) * C).det = A.det * B.det * C.det := by
  rw [Matrix.det_mul, Matrix.det_mul]

/-- Chained: det of A * 1. -/
theorem det_mul_one_chain {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℚ) :
    (A * 1).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_one, mul_one]

/-- Chained: det of 1 * A. -/
theorem det_one_mul_chain {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℚ) :
    (1 * A).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_one, one_mul]

end LeanFormal.IUT.XiFPaper.Mzk1DetBlockChainConsumerActual

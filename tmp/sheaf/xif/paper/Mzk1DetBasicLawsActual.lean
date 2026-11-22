import Mathlib

/-!
# Mzk1DetBasicLawsActual — basic determinant laws (genuine Mathlib proofs)

Status: PENDING-VERIFY. No sorry, no axiom.
Genuine Mathlib determinant laws used by hull-det bookkeeping: mul, one, pow, transpose, diagonal.
 -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DetBasicLawsActual

open Matrix

/-- Genuine: determinant is multiplicative. -/
theorem det_mul_law {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℚ) :
    (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

/-- Genuine: determinant of one is one. -/
theorem det_one_law {n : Type*} [Fintype n] [DecidableEq n] :
    (1 : Matrix n n ℚ).det = 1 :=
  Matrix.det_one

/-- Genuine: determinant of a power. -/
theorem det_pow_law {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℚ) (k : ℕ) :
    (A ^ k).det = A.det ^ k :=
  Matrix.det_pow A k

/-- Genuine: determinant of the transpose. -/
theorem det_transpose_law {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℚ) :
    A.transpose.det = A.det :=
  Matrix.det_transpose A

/-- Genuine: determinant of a diagonal matrix. -/
theorem det_diagonal_law {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℚ) :
    (Matrix.diagonal d).det = ∏ i, d i :=
  Matrix.det_diagonal

end LeanFormal.IUT.XiFPaper.Mzk1DetBasicLawsActual

import Mathlib

/-!
# Mzk1HDDObjectV2Actual — hull-determinant decomposition over matrices (real math)

Status: PENDING-VERIFY. No sorry, no axiom.
HDD = (hull+det) o dsc realized on matrices: hdd = hull * determinant; determinant laws proved.
 -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HDDObjectV2Actual

open Matrix

/-- HDD decomposition data: hull and determinant matrices on a finite index type. -/
structure HDDDecomposition (n : Type*) [Fintype n] [DecidableEq n] where
  hull : Matrix n n ℚ
  determinant : Matrix n n ℚ

/-- Combined HDD readout = hull * determinant. -/
def HDDDecomposition.hdd {n : Type*} [Fintype n] [DecidableEq n]
    (d : HDDDecomposition n) : Matrix n n ℚ :=
  d.hull * d.determinant

/-- Genuine theorem: determinant of the HDD readout is the product of determinants. -/
theorem hdd_det {n : Type*} [Fintype n] [DecidableEq n] (d : HDDDecomposition n) :
    d.hdd.det = d.hull.det * d.determinant.det :=
  Matrix.det_mul d.hull d.determinant

/-- Genuine theorem: determinant of the k-th HDD readout power. -/
theorem hdd_det_pow {n : Type*} [Fintype n] [DecidableEq n] (d : HDDDecomposition n) (k : ℕ) :
    (d.hdd ^ k).det = (d.hull.det * d.determinant.det) ^ k := by
  rw [Matrix.det_pow, hdd_det]

end LeanFormal.IUT.XiFPaper.Mzk1HDDObjectV2Actual

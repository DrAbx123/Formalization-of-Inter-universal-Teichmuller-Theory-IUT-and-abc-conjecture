import tmp.sheaf.xif.paper.Hull06DetTensorActual

/-!
# Mzk1Hull06DetLawActual — derived determinant log-volume laws from the existing Hull06
asset (new theorems: subtraction form of scaling, product commutativity, unit scaling).
No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Hull06DetLawActual

/-- Derived: the change of the log-volume under c-scaling is (card n) * log c. -/
theorem hull06_det_scaling_sub {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (c : ℝ) (hc : 0 < c) (hA : A.PosDef) :
    hull06MatrixLogDet (c • A) - hull06MatrixLogDet A =
      (Fintype.card n : ℝ) * Real.log c := by
  rw [hull06_det_scaling c hc hA]
  ring

/-- Derived: the log-volume is symmetric under swapping the positive definite factors. -/
theorem hull06_det_mul_comm {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    hull06MatrixLogDet (A * B) = hull06MatrixLogDet (B * A) := by
  rw [hull06_det_mul hA hB, hull06_det_mul hB hA]
  ring

/-- Derived: unit scaling does not change the log-volume. -/
theorem hull06_det_one_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} : hull06MatrixLogDet ((1 : ℝ) • A) = hull06MatrixLogDet A := by
  rw [one_smul]

/-- Derived: scaling by c then by d adds the two log-contributions. -/
theorem hull06_det_scaling_comp {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (c d : ℝ) (hc : 0 < c) (hd : 0 < d) (hA : A.PosDef) :
    hull06MatrixLogDet (c • (d • A)) =
      (Fintype.card n : ℝ) * (Real.log c + Real.log d) + hull06MatrixLogDet A := by
  rw [smul_smul, hull06_det_scaling (c * d) (mul_pos hc hd) hA, Real.log_mul hc.ne' hd.ne']
  ring

#check hull06_det_scaling_sub
#check hull06_det_mul_comm
#check hull06_det_one_smul
#check hull06_det_scaling_comp

end LeanFormal.IUT.XiFPaper.Mzk1Hull06DetLawActual
end

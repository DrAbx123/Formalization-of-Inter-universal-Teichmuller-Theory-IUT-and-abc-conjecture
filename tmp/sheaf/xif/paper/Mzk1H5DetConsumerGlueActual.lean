import tmp.sheaf.xif.paper.Mzk1H5DetScalingLawsActual

/-! # Mzk1H5DetConsumerGlueActual — consumer corollaries of the H5 determinant scaling laws

Small glue module (no new mathematics): derives iterated/inverse scalar combinations from
the already-proved `hull06_det_scaling`, `hull06_det_scaling_compose`,
`hull06_det_scaling_inv` and `hull06_det_pow`.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1H5DetConsumerGlueActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1H5DetScalingLawsActual

universe u

/-- Three-scalar composition: scale successively by c, d, e. -/
theorem hull06_det_scaling_three {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c d e : ℝ} (hc : 0 < c) (hd : 0 < d)
    (he : 0 < e) :
    hull06MatrixLogDet (((c * d) * e) • A) =
      (Fintype.card n : ℝ) * Real.log c +
        (Fintype.card n : ℝ) * Real.log d +
        (Fintype.card n : ℝ) * Real.log e + hull06MatrixLogDet A := by
  rw [hull06_det_scaling ((c * d) * e) (mul_pos (mul_pos hc hd) he) hA,
    Real.log_mul (mul_pos hc hd).ne' he.ne', Real.log_mul hc.ne' hd.ne']
  ring

/-- Inverse of a composed scaling: the log terms subtract. -/
theorem hull06_det_scaling_mul_inv {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    hull06MatrixLogDet ((c * d)⁻¹ • A) =
      -((Fintype.card n : ℝ) * Real.log c + (Fintype.card n : ℝ) * Real.log d) +
        hull06MatrixLogDet A := by
  rw [hull06_det_scaling_inv hA (mul_pos hc hd)]
  rw [Real.log_mul hc.ne' hd.ne']
  ring

/-- Scaling then a positive tensor power: the scalar term is multiplied by the power. -/
theorem hull06_det_scaling_pow_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c : ℝ} (hc : 0 < c) (M : Nat) :
    hull06MatrixLogDet ((c • A) ^ M) =
      (M : ℝ) * ((Fintype.card n : ℝ) * Real.log c + hull06MatrixLogDet A) := by
  rw [hull06_det_pow (hA.smul hc) M, hull06_det_scaling c hc hA]

#check hull06_det_scaling_three
#check hull06_det_scaling_mul_inv
#check hull06_det_scaling_pow_smul

end LeanFormal.IUT.XiFPaper.Mzk1H5DetConsumerGlueActual
end

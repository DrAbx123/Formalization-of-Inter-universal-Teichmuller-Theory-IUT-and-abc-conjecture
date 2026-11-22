import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! Mainline: exp-log inverse law for hull determinant log-volume (real proof). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetExpActual

open LeanFormal.IUT

theorem matrixLogDet_exp_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    Real.exp (matrixLogDet A) = A.det := by
  unfold matrixLogDet
  exact Real.exp_log hA.det_pos

theorem matrixLogDet_eq_zero_iff_det_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    matrixLogDet A = 0 ↔ A.det = 1 := by
  unfold matrixLogDet
  rw [Real.log_eq_zero]
  exact or_iff_left (ne_of_gt hA.det_pos)

end LeanFormal.IUT.XiFPaper.Mzk1HullDetExpActual
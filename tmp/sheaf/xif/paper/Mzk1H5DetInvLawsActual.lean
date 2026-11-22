import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
  Mainline: H5 determinant log laws (identity and inverse) beyond the tree scalings.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5DetInvLawsActual

open LeanFormal.IUT

theorem matrixLogDet_one (n : Type*) [Fintype n] [DecidableEq n] :
    matrixLogDet (1 : Matrix n n ℝ) = 0 := by
  unfold matrixLogDet
  simp

theorem matrixLogDet_inv_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) :
    matrixLogDet A⁻¹ = -matrixLogDet A := by
  unfold matrixLogDet
  rw [Matrix.det_inv, Real.log_inv]

end LeanFormal.IUT.XiFPaper.Mzk1H5DetInvLawsActual
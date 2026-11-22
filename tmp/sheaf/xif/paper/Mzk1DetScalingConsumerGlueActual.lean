import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # Mzk1DetScalingConsumerGlueActual — inverse/additive consumer forms of the det scaling laws

Small glue module (no new mathematics): derives the inverse-scaling and difference forms
of the already-proved `matrixLogDet_smul_posDef` / `matrixLogDet_mul_posDef`.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1DetScalingConsumerGlueActual

open LeanFormal.IUT

universe u

/-- Inverse scaling: the normalization factor subtracts. -/
theorem matrixLogDet_smul_inv {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) {c : Real} (hc : 0 < c) :
    matrixLogDet (c⁻¹ • A) =
      -((Fintype.card n : Real) * Real.log c) + matrixLogDet A := by
  rw [matrixLogDet_smul_posDef c⁻¹ (inv_pos.mpr hc) hA, Real.log_inv]
  ring

/-- Additive form: the scaling correction is exactly `card · log c`. -/
theorem matrixLogDet_smul_sub {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) {c : Real} (hc : 0 < c) :
    matrixLogDet (c • A) - matrixLogDet A = (Fintype.card n : Real) * Real.log c := by
  have h := matrixLogDet_smul_posDef c hc hA
  linarith

/-- Multiplicative log-det is the sum of the two factors' log-dets. -/
theorem matrixLogDet_mul_sub {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n Real} (hA : A.PosDef) (hB : B.PosDef) :
    matrixLogDet (A * B) - matrixLogDet A - matrixLogDet B = 0 := by
  have h := matrixLogDet_mul_posDef hA hB
  linarith

/-- Inverse of a product: the two log-dets subtract. -/
theorem matrixLogDet_inv_eq_neg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) :
    matrixLogDet A⁻¹ = -matrixLogDet A := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  have hdet : A.det * A⁻¹.det = 1 := by
    have := congrArg Matrix.det hmul
    simpa [Matrix.det_mul, Matrix.det_one] using this
  have h2 : A⁻¹.det = (A.det)⁻¹ := eq_inv_of_mul_eq_one_left hdet
  unfold matrixLogDet
  rw [h2, Real.log_inv]

#check matrixLogDet_smul_inv
#check matrixLogDet_smul_sub
#check matrixLogDet_mul_sub
#check matrixLogDet_inv_eq_neg

end LeanFormal.IUT.XiFPaper.Mzk1DetScalingConsumerGlueActual
end

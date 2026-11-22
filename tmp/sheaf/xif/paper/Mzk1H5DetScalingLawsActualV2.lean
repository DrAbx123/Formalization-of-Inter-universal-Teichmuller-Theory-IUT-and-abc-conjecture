import tmp.sheaf.xif.paper.Hull06DetTensorActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
  Mainline: H5 determinant scaling composition laws (real proofs on the tree det
  bookkeeping; no re-proof of matrixLogDet laws themselves).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5DetScalingLawsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Hull06DetTensorActual

/-- Compose the lambda*O scaling law: scaling by c then by d adds both log terms. -/
theorem hull06_det_scaling_compose {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    hull06MatrixLogDet ((c * d) • A) =
      (Fintype.card n : ℝ) * Real.log c +
        (Fintype.card n : ℝ) * Real.log d + hull06MatrixLogDet A := by
  rw [hull06_det_scaling (c * d) (mul_pos hc hd) hA]
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hd)]
  ring

/-- Scaling preserves positive definiteness (re-export for consumers). -/
theorem hull06_det_scaling_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • A).PosDef :=
  hA.smul hc

/-- Inverse scaling: log-det picks up the negative of the scaling term. -/
theorem hull06_det_scaling_inv {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    hull06MatrixLogDet (c⁻¹ • A) =
      -((Fintype.card n : ℝ) * Real.log c) + hull06MatrixLogDet A := by
  rw [hull06_det_scaling c⁻¹ (inv_pos.mpr hc) hA]
  rw [Real.log_inv]
  ring
/-- Positive tensor power law re-export: logDet(A^M) = M * logDet A. -/
theorem hull06_det_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) (M : Nat) :
    hull06MatrixLogDet (A ^ M) = (M : ℝ) * hull06MatrixLogDet A :=
  matrixLogDet_pow_posDef hA M
/-- Positive definiteness gives a positive determinant (log-det well-defined). -/
theorem hull06_det_posDet {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosDef) : 0 < A.det := hA.det_pos

/-- The hull06 log-det is the real log of the determinant (definition). -/
theorem hull06MatrixLogDet_eq_log_det {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : hull06MatrixLogDet A = Real.log A.det := rfl
end LeanFormal.IUT.XiFPaper.Mzk1H5DetScalingLawsActual
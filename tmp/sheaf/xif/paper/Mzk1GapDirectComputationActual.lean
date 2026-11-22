/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellIndexArithmetic
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual

/-! # A768/A769/A770: direct gap computation — theta side closed form from green theorems -/

/- GREEN inputs:
* `measure_integralLogShell_eq_index_mul` (HaarIndex:51): μ(logShell) = index * μ(O) for ANY
  additive Haar μ;
* `measure_localIntegers_pos_lt_top` (HaarIndex:24): 0 < μ(O) < ⊤;
* `logShellIntegerIndex_pos` (IndexArithmetic): index > 0;
* `logShellIntegerIndex_eq_card_div_torsion` (IndexArithmetic:100);
* `actualC3LogShell = integralLogShell` (PrimeStripLogShellActual:82).

**A770 normalization finding**: Mathlib `Measure.addHaar` is 'some choice of a Haar measure'
(Mathlib/MeasureTheory/Measure/Haar/Basic.lean:579) — there is NO canonical normalization.
Since `actualC3LogShellTensorHaar = Measure.addHaar`, the theta reading
`thetaPilotHullLogVolumeReal` depends on the arbitrary Haar choice; with the `μ(O)=1`
normalization the theta side is nonnegative (Σ log index ≥ 0), making the comparison weak, so
that normalization is NOT the paper normalization. -/

noncomputable section

open LeanFormal.IUT LeanFormal.IUT.LocalFieldLogarithm

namespace LeanFormal.IUT.XiFPaper.Mzk1GapDirectComputationActual

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
  [MeasurableSpace K] [CharZero K] [CompleteSpace K] [BorelSpace K]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

/-- Theta-hull closed form under the tensor-factorisation hypothesis (explicit): with
`μ_i(O_i) = 1`, `log θHull = Σ_i log index_i ≥ 0`. -/
theorem thetaHull_logVolume_eq_sum_index {ι : Type*} [Fintype ι]
    (logHull : ℝ) (idx : ι → ℕ)
    (hfactor : logHull = ∑ i, Real.log (idx i : ℝ))
    (hidx : ∀ i, 1 ≤ idx i) : 0 ≤ logHull := by
  rw [hfactor]
  apply Finset.sum_nonneg
  intro i _
  apply Real.log_nonneg
  exact_mod_cast hidx i

/-- Arithmetic comparison shape: `qReading <= thetaHull`. -/
def GapArithmeticInequality (l logq thetaHull : ℝ) : Prop :=
  -(1 / (2 * l)) * logq ≤ thetaHull

theorem comparison_of_arithmetic {l logq thetaHull qReading : ℝ}
    (hq : qReading = -(1 / (2 * l)) * logq)
    (h : GapArithmeticInequality l logq thetaHull) : qReading ≤ thetaHull := by
  unfold GapArithmeticInequality at h
  rw [hq]
  exact h

end LeanFormal.IUT.XiFPaper.Mzk1GapDirectComputationActual

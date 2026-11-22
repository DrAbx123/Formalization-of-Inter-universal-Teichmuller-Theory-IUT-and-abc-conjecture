import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open MeasureTheory
open scoped Pointwise ENNReal NNReal
open LeanFormal.IUT

namespace S1552Probe16

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem distribHaarChar_padicPrimeInv (p : ℕ) [Fact p.Prime] :
    distribHaarChar ℚ_[p]
      (Units.mk0 ((p : ℚ_[p])⁻¹)
        (inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero))) =
      (p : ℝ≥0) := by
  letI : MeasurableSpace ℚ_[p] := borel ℚ_[p]
  letI : BorelSpace ℚ_[p] := ⟨rfl⟩
  let u : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p])
    (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have hchar : distribHaarChar ℚ_[p] u = (p : ℝ≥0)⁻¹ := by
    let μ : Measure ℚ_[p] := Measure.addHaar
    let T : Set ℚ_[p] := Metric.closedBall (0 : ℚ_[p]) 1
    have hTpos : 0 < μ T := by
      apply Measure.measure_pos_of_nonempty_interior μ
      refine ⟨0, ?_⟩
      refine mem_interior_iff_mem_nhds.mpr ?_
      exact Filter.mem_of_superset
        (Metric.isOpen_ball.mem_nhds (by simp : (0 : ℚ_[p]) ∈ Metric.ball 0 1))
        (by simp [T, Metric.ball_subset_closedBall])
    have hTfin : μ T < ⊤ := by
      simp only [T]
      exact isCompact_closedBall (0 : ℚ_[p]) 1 |>.measure_lt_top
    refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hTpos.ne' hTfin.ne ?_
    have h := LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
      (p := p) (M := ℚ_[p]) μ T
    have hfin : Module.finrank ℚ_[p] ℚ_[p] = 1 := Module.finrank_self ℚ_[p]
    rw [hfin] at h
    simpa [u, Units.smul_def, ENNReal.coe_inv, ENNReal.coe_natCast,
      ENNReal.coe_pow] using h
  have hu : u⁻¹ = Units.mk0 ((p : ℚ_[p])⁻¹)
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)) := by
    ext
    simp [u]
  rw [← hu]
  rw [show (distribHaarChar ℚ_[p]) u⁻¹ = ((distribHaarChar ℚ_[p]) u)⁻¹ from map_inv _ _]
  rw [hchar, inv_inv]

end S1552Probe16

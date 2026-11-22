import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesEval
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.NumberTheory.Padics.PadicNumbers

open scoped BigOperators
open PowerSeries
open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic

set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Node09TateQSeriesAnalyticPartialActual

local instance fivePrimeFactPartial : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- A formal power series over Z_5 evaluates to an analytic function of q at q=5:
the coefficient sequence is bounded by 1, so the ofScalars radius is at least 1,
and 5 lies strictly inside the unit disk. -/
theorem analyticAt_padicPowerSeriesEval (f : PowerSeries (PadicInt 5)) :
    AnalyticAt ℚ_[5] (fun q : ℚ_[5] => padicPowerSeriesEval f q) 5 := by
  let c : ℕ → ℚ_[5] := fun n => ((f.coeff n : PadicInt 5) : ℚ_[5])
  let p : FormalMultilinearSeries ℚ_[5] ℚ_[5] ℚ_[5] :=
    FormalMultilinearSeries.ofScalars ℚ_[5] c
  have hc : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    exact norm_coeff_padicPowerSeries_le_one f n
  have hp : ∀ n, ‖p n‖ ≤ 1 := by
    intro n
    change ‖c n • ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[5] n ℚ_[5]‖ ≤ 1
    calc ‖c n • ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[5] n ℚ_[5]‖
        ≤ ‖c n‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[5] n ℚ_[5]‖ :=
          ContinuousMultilinearMap.opNorm_smul_le (c n) (ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[5] n ℚ_[5])
      _ = ‖c n‖ * 1 := by rw [ContinuousMultilinearMap.norm_mkPiAlgebraFin]
      _ ≤ 1 * 1 := by exact mul_le_mul_of_nonneg_right (hc n) (by norm_num : (0 : ℝ) ≤ 1)
      _ = 1 := by norm_num
  have hrad : (1 : ENNReal) ≤ p.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound (p := p) (C := 1) (r := 1) ?_
    intro n
    simpa using hp n
  have h51 : (‖(5 : ℚ_[5])‖₊ : ENNReal) < 1 := by
    have h : ‖(5 : ℚ_[5])‖ < 1 := Padic.norm_p_lt_one
    exact ENNReal.coe_lt_coe.mpr h
  have h5 : (‖(5 : ℚ_[5])‖₊ : ENNReal) < p.radius :=
    lt_of_lt_of_le h51 hrad
  have hmem : (5 : ℚ_[5]) ∈ Metric.eball (0 : ℚ_[5]) p.radius :=
    mem_eball_zero_iff.mpr h5
  have hana : AnalyticAt ℚ_[5] p.sum 5 := p.analyticOnNhd 5 hmem
  have hfun : p.sum = fun q : ℚ_[5] => padicPowerSeriesEval f q := by
    funext q
    rw [show p.sum q = ∑' n : ℕ, c n • q ^ n from
      FormalMultilinearSeries.ofScalars_sum_eq c q]
    rw [padicPowerSeriesEval]
    apply tsum_congr
    intro n
    simp [c, smul_eq_mul]
  rwa [hfun] at hana

end LeanFormal.IUT.XiFPaper.Node09TateQSeriesAnalyticPartialActual

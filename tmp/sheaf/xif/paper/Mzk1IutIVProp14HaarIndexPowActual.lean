/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IutIVProp14HaarIndexActual
import tmp.sheaf.xif.paper.Mzk1IutIVProp14IndexCardActual
import Mathlib
import Mathlib.Tactic

/-! # IUT IV Prop 1.4: mu(Lambda)=p^h mu(O) from Gamma card -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14HaarIndexPowActual
open MeasureTheory
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14HaarIndexActual
open LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14IndexCardActual
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
variable {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

theorem mu_lambda_toReal_eq_pow_mul (h : Nat)
    (hc : Nat.card (LogShellIntegerQuotient (K := K) (p := p)) = p ^ h)
    (μ : MeasureTheory.Measure K) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (hO : μ (Integers K : Set K) ≠ ⊤) :
    (μ (integralLogShell (K := K) (p := p) : Set K)).toReal =
      (p : ℝ) ^ h * (μ (Integers K : Set K)).toReal := by
  rw [mu_lambda_toReal_eq_index_mul (K := K) (p := p) μ hO]
  rw [logShellIntegerIndex_eq_pow_of_card_eq (K := K) (p := p) hc]
  norm_cast

end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14HaarIndexPowActual

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex
import Mathlib.Tactic

/-! # IUT IV Prop 1.4: Haar index wrapper mu(Lambda)=index*mu(O) -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14HaarIndexActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

theorem mu_lambda_eq_index_mul
    (K : Type*) [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
    (p : Nat) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (μ : Measure K) [Measure.IsAddHaarMeasure μ] :
    μ (integralLogShell (K := K) (p := p) : Set K) =
      (logShellIntegerIndex (K := K) (p := p) : ENNReal) *
        μ (Integers K : Set K) :=
  measure_integralLogShell_eq_index_mul (K := K) (p := p) μ

theorem mu_lambda_toReal_eq_index_mul
    (K : Type*) [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
    (p : Nat) [Fact p.Prime] [NormedAlgebra ℚ_[p] K]
    (μ : Measure K) [Measure.IsAddHaarMeasure μ]
    (hO : μ (Integers K : Set K) ≠ ⊤) :
    (μ (integralLogShell (K := K) (p := p) : Set K)).toReal =
      (logShellIntegerIndex (K := K) (p := p) : ℝ) *
        (μ (Integers K : Set K)).toReal := by
  rw [mu_lambda_eq_index_mul (K := K) (p := p) (μ := μ)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14HaarIndexActual

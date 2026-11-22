/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1IutIVProp14HaarIndexPowActual
import tmp.sheaf.xif.paper.IutIVProp14VolumeActual
import Mathlib.Tactic

/-! # IUT IV Prop 1.4: Haar-index volume ratio (h from #Gamma) -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14VolumeRatioHaarActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.IutIVProp14VolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14HaarIndexPowActual
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
variable {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K]

theorem volume_ratio_eq_pow_of_haar (h d s f m : Nat)
    (hc : Nat.card (LogShellIntegerQuotient (K := K) (p := p)) = p ^ h)
    (μ : MeasureTheory.Measure K) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (hO : μ (Integers K : Set K) ≠ ⊤)
    (μL : ℝ)
    (hexp : h + f + m = s * d)
    (hL : μL = (p : ℝ) ^ (-(s * d : ℤ)) *
      (μ (integralLogShell (K := K) (p := p) : Set K)).toReal) :
    μL = (p : ℝ) ^ (-(f + m : ℤ)) * (μ (Integers K : Set K)).toReal := by
  have hμΛ := mu_lambda_toReal_eq_pow_mul (K := K) (p := p) h hc μ hO
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.Prime.pos (Fact.out)
  exact volume_ratio_eq_pow (p := (p : ℝ)) hp0
    d s h f m (μ (Integers K : Set K)).toReal
    (μ (integralLogShell (K := K) (p := p) : Set K)).toReal μL hexp hμΛ hL

end LeanFormal.IUT.XiFPaper.Mzk1IutIVProp14VolumeRatioHaarActual

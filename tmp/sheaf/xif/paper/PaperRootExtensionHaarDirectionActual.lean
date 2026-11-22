import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import tmp.sheaf.xif.paper.PaperRootExtensionFieldScalingHaarActual

/-! # Direction audit for Haar scaling in dimension one -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators Pointwise ENNReal

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarDirectionActual

open LeanFormal.IUT
open MeasureTheory
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingHaarActual

/-- One-dimensional Qp direction: additive Haar of p • S is ||p|| times Haar(S),
not its inverse. -/
theorem qp_prime_smul_measure_oneDim
    {p : Nat} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [Measure.IsAddHaarMeasure μ] (S : Set ℚ_[p]) :
    μ ((p : ℚ_[p]) • S) =
      ENNReal.ofReal ‖(p : ℚ_[p])‖ * μ S := by
  have h := LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
    (p := p) (M := ℚ_[p]) μ S
  rw [Module.finrank_self, pow_one] at h
  rw [h, Padic.norm_p, ENNReal.ofReal_inv_of_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos),
    ENNReal.ofReal_natCast]

/-- The inverse direction is ruled out: the one-dimensional factor is the norm. -/
theorem qp_prime_smul_factor_eq_norm
    {p : Nat} [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [Measure.IsAddHaarMeasure μ]
    {S : Set ℚ_[p]} (hS : μ S ≠ 0) (hSfin : μ S ≠ ⊤) :
    μ ((p : ℚ_[p]) • S) / μ S = ENNReal.ofReal ‖(p : ℚ_[p])‖ := by
  rw [qp_prime_smul_measure_oneDim (p := p) μ S, ENNReal.mul_div_cancel_right hS hSfin]



end LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarDirectionActual

end

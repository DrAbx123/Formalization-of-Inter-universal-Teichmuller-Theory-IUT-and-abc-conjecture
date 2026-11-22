import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open scoped BigOperators Pointwise ENNReal
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2730RegionScalingActual

open LeanFormal.IUT
open MeasureTheory

universe u

variable {p : Nat} [Fact p.Prime] {M : Type} [NormedAddCommGroup M]
variable [NormedSpace ℚ_[p] M] [FiniteDimensional ℚ_[p] M]
variable [MeasurableSpace M] [BorelSpace M]
variable (μ : Measure M) [Measure.IsAddHaarMeasure μ]

/-- The point-dependent scaled region `a • U`, the actual scaling candidate for
the comparison region (not the fixed identity scaling). -/
def S2730PointScaledRegion (a : M) (U : Set M) : Set M := (fun x => a • x) '' U

/-- Actual prime-p Haar scaling: the `p`-scaled region has measure
`p^{-finrank} * μ U`. -/
theorem S2730_prime_region_volume (U : Set M) :
    μ ((p : ℚ_[p]) • U) =
      ((p : ENNReal) ^ Module.finrank ℚ_[p] M)⁻¹ * μ U :=
  FinitePadicHaarScaling.measure_prime_smul_finiteDimensional μ U

/-- Actual prime-p logarithmic scaling formula. -/
theorem S2730_prime_region_log_volume {U : Set M}
    (hpos : 0 < μ U) (hfin : μ U < ⊤) :
    Real.log (μ ((p : ℚ_[p]) • U)).toReal =
      -(Module.finrank ℚ_[p] M : Real) * Real.log (p : Real) +
        Real.log (μ U).toReal :=
  FinitePadicHaarScaling.log_measure_prime_smul_finiteDimensional
    μ hpos hfin

/-- Exact missing general scaling input: Haar measure of a general scalar-scaled
region is the norm-power multiple of the original measure.  This is the
point-dependent scaling formula needed for `λ := point`; only the prime-p case
is actual in the tree. -/
def S2730GeneralHaarScaling : Prop :=
  ∀ (a : ℚ_[p]) (U : Set M),
    μ (a • U) =
      (‖a‖ : ENNReal) ^ Module.finrank ℚ_[p] M * μ U

/-- Conditional point-dependent region-volume formula from the missing general
scaling input. -/
theorem S2730_regionVolume_eq_scaling_of
    (hscale : S2730GeneralHaarScaling (μ := μ)) (a : ℚ_[p]) (U : Set M) :
    μ (S2730PointScaledRegion (M := M) (a • (1 : M)) U) =
      (‖a‖ : ENNReal) ^ Module.finrank ℚ_[p] M * μ U :=
  hscale a U

#check S2730PointScaledRegion
#check S2730_prime_region_volume
#check S2730_prime_region_log_volume
#check S2730GeneralHaarScaling
#check S2730_regionVolume_eq_scaling_of

end LeanFormal.IUT.XiFPaper.S2730RegionScalingActual
end

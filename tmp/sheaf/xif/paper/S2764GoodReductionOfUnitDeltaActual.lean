import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange

noncomputable section
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2764GoodReductionOfUnitDeltaActual

variable {R K : Type*}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integral equation whose integral-model discriminant is a unit has good
reduction. -/
theorem hasGoodReduction_of_isUnit_integralModel_delta
    (W : WeierstrassCurve K) [W.IsIntegral R]
    (hΔ : IsUnit (W.integralModel R).Δ) :
    W.HasGoodReduction R := by
  have hval : (IsDiscreteValuationRing.maximalIdeal R).valuation K W.Δ = 1 := by
    rw [← WeierstrassCurve.integralModel_Δ_eq R W]
    exact (IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem
      (K := K) |>.mpr (IsLocalRing.notMem_maximalIdeal.mpr hΔ)
  letI : W.IsMinimal R :=
    isMinimal_of_isIntegral_valuation_Δ_eq_one R W hval
  exact { goodReduction := hval }

#check hasGoodReduction_of_isUnit_integralModel_delta
#print axioms hasGoodReduction_of_isUnit_integralModel_delta

end LeanFormal.IUT.XiFPaper.S2764GoodReductionOfUnitDeltaActual
end

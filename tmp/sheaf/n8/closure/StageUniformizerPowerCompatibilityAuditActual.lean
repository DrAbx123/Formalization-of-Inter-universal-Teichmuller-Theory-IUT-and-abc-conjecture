import tmp.sheaf.n8.closure.StageUniformizerSectionAuditActual

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Iut.SourceFinitePlaceReconstruction

universe u

variable {K : Type u} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)

/-- If π has normalized valuation one at the source, its transition has
normalized valuation equal to the ramification index. -/
theorem stageUnitTransition_uniformizer_valuation
    (π : ∀ stage : StageIndex place, stageˣ)
    (hπ : ∀ stage : StageIndex place,
      stageNormalizedAdditiveValuation place stage
        (Additive.ofMul (π stage)) = 1)
    {source target : StageIndex place} (map : source ≤ target) :
    stageNormalizedAdditiveValuation place target
      (Additive.ofMul (stageUnitTransition place map (π source))) =
      (stageRamificationIndex place map : ℤ) := by
  rw [stageNormalizedAdditiveValuation_transition, hπ source,
    stageNormalizedAdditiveTransition_eq_ramification_mul]
  simp

/-- Likewise, the e-th power of a valuation-one target uniformizer has
normalized valuation e. -/
theorem stageUniformizer_pow_valuation
    (π : ∀ stage : StageIndex place, stageˣ)
    (hπ : ∀ stage : StageIndex place,
      stageNormalizedAdditiveValuation place stage
        (Additive.ofMul (π stage)) = 1)
    (stage : StageIndex place) (n : ℕ) :
    stageNormalizedAdditiveValuation place stage
      (Additive.ofMul (π stage ^ n)) = (n : ℤ) := by
  rw [show Additive.ofMul (π stage ^ n) =
      n • Additive.ofMul (π stage) by simp]
  rw [map_nsmul, hπ stage]
  simp

/-- Power-compatible uniformizer data is valuation-consistent: the transition
valuation and the e-th-power valuation are both e, so no contradiction comes
from valuations alone. -/
theorem stageUniformizer_powerCompatibility_valuation_consistent
    (π : ∀ stage : StageIndex place, stageˣ)
    (hπ : ∀ stage : StageIndex place,
      stageNormalizedAdditiveValuation place stage
        (Additive.ofMul (π stage)) = 1)
    {source target : StageIndex place} (map : source ≤ target) :
    stageNormalizedAdditiveValuation place target
      (Additive.ofMul (stageUnitTransition place map (π source))) =
    stageNormalizedAdditiveValuation place target
      (Additive.ofMul (π target ^ stageRamificationIndex place map)) := by
  rw [stageUnitTransition_uniformizer_valuation place π hπ map,
    stageUniformizer_pow_valuation place π hπ target
    (stageRamificationIndex place map)]

end Iut.SourceFinitePlaceReconstruction

end

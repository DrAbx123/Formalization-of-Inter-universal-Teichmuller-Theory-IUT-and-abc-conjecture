import Iut.Foundations.SourceFiniteStageModelFrobenioid

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Iut.SourceFinitePlaceReconstruction

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- A stage-global compatible uniformizer section.  This is an exact
source object, not asserted to exist. -/
structure StageUniformizerSectionCompatible
    (place : NumberField.FinitePlace K) where
  pi : ∀ stage : StageIndex place, stageˣ
  valuation_eq_one : ∀ stage : StageIndex place,
    stageNormalizedAdditiveValuation place stage
      (Additive.ofMul (pi stage)) = 1
  transition_eq :
    ∀ {source target : StageIndex place} (map : source ≤ target),
      stageUnitTransition place map (pi source) = pi target

/-- If a compatible valuation-one section exists, every stage transition has
ramification index one. -/
theorem stageRamificationIndex_eq_one_of_uniformizerSection
    (place : NumberField.FinitePlace K)
    (S : StageUniformizerSectionCompatible (K := K) place)
    {source target : StageIndex place} (map : source ≤ target) :
    stageRamificationIndex place map = 1 := by
  have hval := congrArg
    (fun unit : targetˣ =>
      stageNormalizedAdditiveValuation place target
        (Additive.ofMul unit)) (S.transition_eq map)
  rw [stageNormalizedAdditiveValuation_transition, S.valuation_eq_one source,
    S.valuation_eq_one target] at hval
  rw [stageNormalizedAdditiveTransition_eq_ramification_mul] at hval
  have he : (stageRamificationIndex place map : ℤ) = 1 := by
    simpa using hval
  exact_mod_cast he

/-- Obstruction form: if some transition has ramification index ≠ 1, no
compatible valuation-one global section exists. -/
theorem no_compatible_uniformizerSection_of_ramification_ne_one
    (place : NumberField.FinitePlace K)
    {source target : StageIndex place} (map : source ≤ target)
    (h : stageRamificationIndex place map ≠ 1) :
    ¬ Nonempty (StageUniformizerSectionCompatible (K := K) place) := by
  rintro ⟨S⟩
  exact h (stageRamificationIndex_eq_one_of_uniformizerSection place S map)

end Iut.SourceFinitePlaceReconstruction

end

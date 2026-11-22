import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiEvaluationActual

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# Evaluation/retraction surjectivity criterion

Precise criterion: the corrected unit comparison is surjective exactly when an
actual corrected evaluation/retraction datum exists.  The forward direction is
the retraction/constant splitting of the induced unit map; the converse uses
the actual evaluation datum carried by the comparison.  The separated-unit
obstruction rules out surjectivity when no evaluation exists.  No point or
surjectivity is fabricated.
-/

namespace LeanFormal.IUT.SourcePsiEvaluationSurjectivityCriterion

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiActualMinimalModelInhabited
open LeanFormal.IUT.SourcePsiEvaluationActual
open LeanFormal.IUT.SourcePsiEvaluationObstruction
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (A : SourcePsiActualMinimalModelCorrected S v)

/-- The corrected unit comparison is surjective when some actual evaluation
datum induces a surjective unit map. -/
def CorrectedUnitComparisonSurjective : Prop :=
  ∃ E : SourcePsiCorrectedEvaluationData S v A,
    Function.Surjective (sourcePsiCorrectedUnitsToCompletion S v A E)

/-- Exact existence of the evaluation/retraction datum. -/
def CorrectedEvaluationDataExists : Prop :=
  Nonempty (SourcePsiCorrectedEvaluationData S v A)

/-- The precise equivalence: unit-comparison surjectivity iff an actual
evaluation/retraction datum exists. -/
theorem correctedUnitComparisonSurjective_iff_evaluationData :
    CorrectedUnitComparisonSurjective S v A ↔
      CorrectedEvaluationDataExists S v A := by
  constructor
  · rintro ⟨E, _⟩
    exact ⟨E⟩
  · rintro ⟨E⟩
    exact ⟨E, sourcePsiCorrectedUnitsToCompletion_surjective S v A E⟩

/-- A corrected integral point is sufficient for unit-comparison surjectivity. -/
theorem correctedUnitComparisonSurjective_of_point
    (P : SourcePsiCorrectedIntegralPoint S v A) :
    CorrectedUnitComparisonSurjective S v A :=
  (correctedUnitComparisonSurjective_iff_evaluationData S v A).mpr
    ⟨sourcePsiCorrectedEvaluationDataOfPoint S v A P⟩

theorem correctedUnitComparisonSurjective_of_pointResidual
    (h : SourcePsiCorrectedIntegralPointResidual S v A) :
    CorrectedUnitComparisonSurjective S v A := by
  rcases h with ⟨P⟩
  exact correctedUnitComparisonSurjective_of_point S v A P

/-- A separated unit obstructs the corrected unit comparison. -/
theorem not_correctedUnitComparisonSurjective_of_separatedUnit
    {u : (SourcePsiCorrectedCoordinateRing S v A)ˣ}
    (hu : IsSeparatedCorrectedUnit S v A u) :
    ¬ CorrectedUnitComparisonSurjective S v A := by
  intro h
  exact (not_correctedEvaluationData_of_separatedUnit S v A hu)
    ((correctedUnitComparisonSurjective_iff_evaluationData S v A).mp h)

/-- Conversely, absence of an evaluation datum is exactly absence of a
surjective corrected unit comparison. -/
theorem not_correctedUnitComparisonSurjective_iff_no_evaluation :
    (¬ CorrectedUnitComparisonSurjective S v A) ↔
      ¬ CorrectedEvaluationDataExists S v A :=
  not_congr (correctedUnitComparisonSurjective_iff_evaluationData S v A)

/-- The unit comparison is exactly conditional on the evaluation/retraction
datum: no unconditional surjectivity is claimed. -/
theorem correctedUnitComparison_conditional :
    CorrectedUnitComparisonSurjective S v A ↔
      (∃ E : SourcePsiCorrectedEvaluationData S v A,
        Function.Surjective (sourcePsiCorrectedUnitsToCompletion S v A E)) :=
  Iff.rfl

/-- The actual unit map is surjective for every supplied evaluation datum. -/
theorem correctedUnitComparison_surjective_of_evaluation
    (E : SourcePsiCorrectedEvaluationData S v A) :
    Function.Surjective (sourcePsiCorrectedUnitsToCompletion S v A E) :=
  sourcePsiCorrectedUnitsToCompletion_surjective S v A E

/-- Evaluation existence is equivalent to point residual plus evaluation; the
point is sufficient but not claimed necessary. -/
theorem correctedUnitComparison_of_point_or_evaluation :
    (SourcePsiCorrectedIntegralPointResidual S v A →
      CorrectedUnitComparisonSurjective S v A) ∧
    (SourcePsiCorrectedEvaluationResidual S v A →
      CorrectedUnitComparisonSurjective S v A) :=
  ⟨correctedUnitComparisonSurjective_of_pointResidual S v A,
    fun h => (correctedUnitComparisonSurjective_iff_evaluationData S v A).mpr h⟩

end LeanFormal.IUT.SourcePsiEvaluationSurjectivityCriterion
end
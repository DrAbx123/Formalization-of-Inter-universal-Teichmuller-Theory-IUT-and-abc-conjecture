import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiEvaluationObstruction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiActualMinimalModelInhabited

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# Actual evaluation/retraction from the corrected model

From the corrected actual Mathlib minimal model, this file constructs the
integral coordinate ring, integral points, the evaluation/retraction datum, the
induced unit map, and the exact separated-unit obstruction.  No point or
evaluation is fabricated when absent.
-/

namespace LeanFormal.IUT.SourcePsiEvaluationActual

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiActualMinimalModelInhabited
open LeanFormal.IUT.SourcePsiEvaluationObstruction
open LeanFormal.IUT.SourcePsiIntegralModelUnitMapExistence
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (A : SourcePsiActualMinimalModelCorrected S v)

/-- The actual integral coordinate ring of the corrected model. -/
noncomputable abbrev SourcePsiCorrectedCoordinateRing : Type u :=
  WeierstrassCurve.Affine.CoordinateRing A.curve

/-- An actual integral point of the corrected model. -/
structure SourcePsiCorrectedIntegralPoint : Type u where
  x : SourcePsiCompletionIntegers S v
  y : SourcePsiCompletionIntegers S v
  equation :
    A.curve.polynomial.evalEval (x : SourcePsiCompletionField S v)
      (y : SourcePsiCompletionField S v) = 0

/-- Evaluation at an actual corrected integral point. -/
noncomputable def sourcePsiCorrectedEvaluationOfPoint
    (P : SourcePsiCorrectedIntegralPoint S v A) :
    SourcePsiCorrectedCoordinateRing S v A →+* SourcePsiCompletionIntegers S v :=
  AdjoinRoot.lift
    (Polynomial.evalRingHom (P.x : SourcePsiCompletionIntegers S v))
    P.y
    (by
      simpa [SourcePsiCorrectedCoordinateRing] using P.equation)

theorem sourcePsiCorrectedEvaluationOfPoint_algebraMap
    (P : SourcePsiCorrectedIntegralPoint S v A) :
    (sourcePsiCorrectedEvaluationOfPoint S v A P).comp
        (algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCorrectedCoordinateRing S v A)) =
      RingHom.id (SourcePsiCompletionIntegers S v) := by
  ext r
  simp [sourcePsiCorrectedEvaluationOfPoint, AdjoinRoot.lift_algebraMap]

/-- An actual evaluation/retraction datum of the corrected coordinate ring. -/
structure SourcePsiCorrectedEvaluationData where
  evaluation : SourcePsiCorrectedCoordinateRing S v A →+*
    SourcePsiCompletionIntegers S v
  evaluation_algebraMap :
    evaluation.comp (algebraMap (SourcePsiCompletionIntegers S v)
      (SourcePsiCorrectedCoordinateRing S v A)) =
      RingHom.id (SourcePsiCompletionIntegers S v)

noncomputable def sourcePsiCorrectedEvaluationDataOfPoint
    (P : SourcePsiCorrectedIntegralPoint S v A) :
    SourcePsiCorrectedEvaluationData S v A where
  evaluation := sourcePsiCorrectedEvaluationOfPoint S v A P
  evaluation_algebraMap := sourcePsiCorrectedEvaluationOfPoint_algebraMap S v A P

/-- The induced unit map from corrected coordinate-ring units to completion units. -/
noncomputable def sourcePsiCorrectedUnitsToCompletion
    (E : SourcePsiCorrectedEvaluationData S v A) :
    (SourcePsiCorrectedCoordinateRing S v A)ˣ →*
      (SourcePsiCompletionIntegers S v)ˣ :=
  Units.map E.evaluation.toMonoidHom

theorem sourcePsiCorrectedUnitsToCompletion_constant
    (E : SourcePsiCorrectedEvaluationData S v A)
    (r : (SourcePsiCompletionIntegers S v)ˣ) :
    sourcePsiCorrectedUnitsToCompletion S v A E
        (Units.map (algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCorrectedCoordinateRing S v A)).toMonoidHom r) = r := by
  ext
  have hret := congrFun (congrArg DFunLike.coe E.evaluation_algebraMap)
    (r : SourcePsiCompletionIntegers S v)
  simpa [sourcePsiCorrectedUnitsToCompletion] using hret

theorem sourcePsiCorrectedUnitsToCompletion_surjective
    (E : SourcePsiCorrectedEvaluationData S v A) :
    Function.Surjective (sourcePsiCorrectedUnitsToCompletion S v A E) := by
  intro r
  refine ⟨Units.map (algebraMap (SourcePsiCompletionIntegers S v)
    (SourcePsiCorrectedCoordinateRing S v A)).toMonoidHom r, ?_⟩
  exact sourcePsiCorrectedUnitsToCompletion_constant S v A E r

/-- Exact separated-unit obstruction for the corrected coordinate ring. -/
def IsSeparatedCorrectedUnit
    (u : (SourcePsiCorrectedCoordinateRing S v A)ˣ) : Prop :=
  ∀ r : SourcePsiCompletionIntegers S v,
    IsUnit ((u : SourcePsiCorrectedCoordinateRing S v A) -
      algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiCorrectedCoordinateRing S v A) r)

theorem not_correctedEvaluationData_of_separatedUnit
    {u : (SourcePsiCorrectedCoordinateRing S v A)ˣ}
    (hu : IsSeparatedCorrectedUnit S v A u) :
    ¬ Nonempty (SourcePsiCorrectedEvaluationData S v A) := by
  rintro ⟨E⟩
  let r : SourcePsiCompletionIntegers S v := E.evaluation (u : SourcePsiCorrectedCoordinateRing S v A)
  have hzero : E.evaluation ((u : SourcePsiCorrectedCoordinateRing S v A) -
      algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiCorrectedCoordinateRing S v A) r) = 0 := by
    simp [r]
  have hunit : IsUnit ((u : SourcePsiCorrectedCoordinateRing S v A) -
      algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiCorrectedCoordinateRing S v A) r) := hu r
  have himage : IsUnit (E.evaluation ((u : SourcePsiCorrectedCoordinateRing S v A) -
      algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiCorrectedCoordinateRing S v A) r)) := hunit.map E.evaluation
  rw [hzero] at himage
  exact not_isUnit_zero himage

theorem not_correctedPoint_of_separatedUnit
    {u : (SourcePsiCorrectedCoordinateRing S v A)ˣ}
    (hu : IsSeparatedCorrectedUnit S v A u)
    (P : SourcePsiCorrectedIntegralPoint S v A) : False :=
  (not_correctedEvaluationData_of_separatedUnit S v A hu)
    ⟨sourcePsiCorrectedEvaluationDataOfPoint S v A P⟩

/-- Exact corrected point residual. -/
def SourcePsiCorrectedIntegralPointResidual : Prop :=
  Nonempty (SourcePsiCorrectedIntegralPoint S v A)

/-- Exact corrected evaluation residual. -/
def SourcePsiCorrectedEvaluationResidual : Prop :=
  Nonempty (SourcePsiCorrectedEvaluationData S v A)

theorem correctedEvaluationResidual_of_point
    (h : SourcePsiCorrectedIntegralPointResidual S v A) :
    SourcePsiCorrectedEvaluationResidual S v A := by
  rcases h with ⟨P⟩
  exact ⟨sourcePsiCorrectedEvaluationDataOfPoint S v A P⟩

/-- Point gives evaluation, evaluation gives unit map/surjectivity; separated
unit obstructs both. -/
theorem sourcePsiEvaluationActual_boundary :
    (SourcePsiCorrectedIntegralPointResidual S v A →
      SourcePsiCorrectedEvaluationResidual S v A) ∧
    (∀ E : SourcePsiCorrectedEvaluationData S v A,
      Function.Surjective (sourcePsiCorrectedUnitsToCompletion S v A E)) :=
  ⟨correctedEvaluationResidual_of_point S v A,
    fun E => sourcePsiCorrectedUnitsToCompletion_surjective S v A E⟩

/-! ## Coordinate and retraction laws -/ 

theorem sourcePsiCorrectedEvaluationOfPoint_algebraMap_apply
    (P : SourcePsiCorrectedIntegralPoint S v A)
    (r : SourcePsiCompletionIntegers S v) :
    sourcePsiCorrectedEvaluationOfPoint S v A P
        (algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCorrectedCoordinateRing S v A) r) = r :=
  by
  have h := congrFun (congrArg DFunLike.coe
    (sourcePsiCorrectedEvaluationOfPoint_algebraMap S v A P)) r
  simpa using h

theorem sourcePsiCorrectedEvaluationOfPoint_root
    (P : SourcePsiCorrectedIntegralPoint S v A) :
    sourcePsiCorrectedEvaluationOfPoint S v A P
        (AdjoinRoot.root A.curve.polynomial) = P.y :=
  AdjoinRoot.lift_root

theorem sourcePsiCorrectedEvaluationData_apply_constant
    (E : SourcePsiCorrectedEvaluationData S v A)
    (r : SourcePsiCompletionIntegers S v) :
    E.evaluation (algebraMap (SourcePsiCompletionIntegers S v)
      (SourcePsiCorrectedCoordinateRing S v A) r) = r := by
  have h := congrFun (congrArg DFunLike.coe E.evaluation_algebraMap) r
  simpa using h

theorem sourcePsiCorrectedUnitsToCompletion_mul
    (E : SourcePsiCorrectedEvaluationData S v A)
    (x y : (SourcePsiCorrectedCoordinateRing S v A)ˣ) :
    sourcePsiCorrectedUnitsToCompletion S v A E (x * y) =
      sourcePsiCorrectedUnitsToCompletion S v A E x *
        sourcePsiCorrectedUnitsToCompletion S v A E y :=
  map_mul _ x y

theorem sourcePsiCorrectedUnitsToCompletion_one
    (E : SourcePsiCorrectedEvaluationData S v A) :
    sourcePsiCorrectedUnitsToCompletion S v A E 1 = 1 :=
  map_one _

theorem sourcePsiCorrectedUnitsToCompletion_inv
    (E : SourcePsiCorrectedEvaluationData S v A)
    (x : (SourcePsiCorrectedCoordinateRing S v A)ˣ) :
    sourcePsiCorrectedUnitsToCompletion S v A E x⁻¹ =
      (sourcePsiCorrectedUnitsToCompletion S v A E x)⁻¹ :=
  map_inv _ x

/-- A separated corrected unit is nonconstant. -/
theorem IsSeparatedCorrectedUnit.not_constant
    {u : (SourcePsiCorrectedCoordinateRing S v A)ˣ}
    (hu : IsSeparatedCorrectedUnit S v A u) :
    ¬ ∃ r : (SourcePsiCompletionIntegers S v)ˣ,
      u = Units.map (algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiCorrectedCoordinateRing S v A)).toMonoidHom r := by
  rintro ⟨r, rfl⟩
  have hzero : ((Units.map (algebraMap (SourcePsiCompletionIntegers S v)
      (SourcePsiCorrectedCoordinateRing S v A)).toMonoidHom r :
        SourcePsiCorrectedCoordinateRing S v A) -
      algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiCorrectedCoordinateRing S v A) (r : SourcePsiCompletionIntegers S v)) = 0 := by
    simp
  have hu' := hu (r : SourcePsiCompletionIntegers S v)
  rw [hzero] at hu'
  exact not_isUnit_zero hu'

/-- The exact obstruction alternative: either an actual point/evaluation exists,
or a separated unit obstructs every evaluation.  The separated unit is not
asserted. -/
theorem sourcePsiEvaluationActual_dichotomy :
    SourcePsiCorrectedIntegralPointResidual S v A ∨
      (∃ u : (SourcePsiCorrectedCoordinateRing S v A)ˣ,
        IsSeparatedCorrectedUnit S v A u) ∨
      SourcePsiCorrectedEvaluationResidual S v A :=
  by
  by_cases hpt : SourcePsiCorrectedIntegralPointResidual S v A
  · exact Or.inl hpt
  · by_cases hsep : ∃ u : (SourcePsiCorrectedCoordinateRing S v A)ˣ,
        IsSeparatedCorrectedUnit S v A u
    · exact Or.inr (Or.inl hsep)
    · exact Or.inr (Or.inr (correctedEvaluationResidual_of_point S v A hpt))

end LeanFormal.IUT.SourcePsiEvaluationActual
end
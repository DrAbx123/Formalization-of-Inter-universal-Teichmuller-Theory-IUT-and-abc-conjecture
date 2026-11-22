import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiTorsionPointEvaluation

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

/-!
# Torsion point selection consumer

This file packages the exact torsion-point selection datum, its affine/integral
point, the induced evaluation and unit-map surjectivity, and the at-infinity /
nonintegral obstructions.  No point or selection is fabricated.
-/

namespace LeanFormal.IUT.SourcePsiTorsionPointSelectionConsumer

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiTorsionPointEvaluation
open LeanFormal.IUT.SourcePsiIntegralUnitMapSurjectivity
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (h : SourcePsiCoefficientsIntegral S v)

/-- Consumer package for a selected torsion point with affine/integral data. -/
structure SourcePsiTorsionSelectionConsumer where
  selection : SourcePsiTorsionPointSelection S v
  affinePoint : SourcePsiTorsionAffineIntegralPoint S v selection
  integralPoint : SourcePsiIntegralPoint S v h
  evaluation : SourcePsiIntegralEvaluationData S v h
  unitMapSurjective : Function.Surjective
    (SourcePsiIntegralUnitMap S v h evaluation)

/-- The actual consumer built from an affine/integral selected torsion point. -/
noncomputable def sourcePsiTorsionSelectionConsumer
    (T : SourcePsiTorsionPointSelection S v)
    (D : SourcePsiTorsionAffineIntegralPoint S v T) :
    SourcePsiTorsionSelectionConsumer S v h where
  selection := T
  affinePoint := D
  integralPoint := sourcePsiIntegralPointOfTorsion S v h D
  evaluation := sourcePsiEvaluationDataOfTorsion S v h D
  unitMapSurjective := sourcePsiTorsionUnitMap_surjective S v h D

theorem consumer_selection
    (T : SourcePsiTorsionPointSelection S v)
    (D : SourcePsiTorsionAffineIntegralPoint S v T) :
    (sourcePsiTorsionSelectionConsumer S v h T D).selection = T :=
  rfl

theorem consumer_affinePoint
    (T : SourcePsiTorsionPointSelection S v)
    (D : SourcePsiTorsionAffineIntegralPoint S v T) :
    (sourcePsiTorsionSelectionConsumer S v h T D).affinePoint = D :=
  rfl

theorem consumer_integralPoint
    (T : SourcePsiTorsionPointSelection S v)
    (D : SourcePsiTorsionAffineIntegralPoint S v T) :
    (sourcePsiTorsionSelectionConsumer S v h T D).integralPoint =
      sourcePsiIntegralPointOfTorsion S v h D :=
  rfl

theorem consumer_evaluation
    (T : SourcePsiTorsionPointSelection S v)
    (D : SourcePsiTorsionAffineIntegralPoint S v T) :
    (sourcePsiTorsionSelectionConsumer S v h T D).evaluation =
      sourcePsiEvaluationDataOfTorsion S v h D :=
  rfl

theorem consumer_unitMap_surjective
    (T : SourcePsiTorsionPointSelection S v)
    (D : SourcePsiTorsionAffineIntegralPoint S v T) :
    Function.Surjective (SourcePsiIntegralUnitMap S v h
      (sourcePsiTorsionSelectionConsumer S v h T D).evaluation) :=
  (sourcePsiTorsionSelectionConsumer S v h T D).unitMapSurjective

/-- Exact selection residual. -/
def SourcePsiTorsionSelectionResidual : Prop :=
  Nonempty (SourcePsiTorsionPointSelection S v)

/-- Exact affine/integral selected point residual. -/
def SourcePsiTorsionAffineIntegralConsumerResidual : Prop :=
  ∃ T : SourcePsiTorsionPointSelection S v,
    Nonempty (SourcePsiTorsionAffineIntegralPoint S v T)

theorem torsionSelectionConsumerResidual_of_affine
    (hD : SourcePsiTorsionAffineIntegralConsumerResidual S v) :
    Nonempty (SourcePsiIntegralEvaluationData S v h) := by
  rcases hD with ⟨T, ⟨D⟩⟩
  exact ⟨sourcePsiEvaluationDataOfTorsion S v h D⟩

/-- At-infinity obstruction consumer. -/
theorem torsionSelection_atInfinity_obstructs
    (T : SourcePsiTorsionPointSelection S v)
    (hinf : SourcePsiTorsionAtInfinity S v T) :
    ¬ Nonempty (SourcePsiTorsionAffineIntegralPoint S v T) :=
  not_torsionAffineIntegralPoint_of_atInfinity S v T hinf

/-- Nonintegral obstruction consumer. -/
theorem torsionSelection_nonintegral_obstructs
    (T : SourcePsiTorsionPointSelection S v)
    (hni : SourcePsiTorsionNonintegral S v T) :
    ¬ Nonempty (SourcePsiTorsionAffineIntegralPoint S v T) :=
  not_torsionAffineIntegralPoint_of_nonintegral S v T hni

/-- The abstract torsion carrier exists, but the actual point selection remains
the exact missing datum. -/
theorem torsionSelection_boundary :
    Nonempty (SourceTorsionCarrier S) ∧
      (SourcePsiTorsionPointSelectionResidual S v ↔
        Nonempty (SourcePsiTorsionPointSelection S v)) :=
  ⟨sourcePsiTorsionCarrier_nonempty S v,
    sourcePsiTorsionPointSelectionResidual_iff S v⟩

end LeanFormal.IUT.SourcePsiTorsionPointSelectionConsumer
end
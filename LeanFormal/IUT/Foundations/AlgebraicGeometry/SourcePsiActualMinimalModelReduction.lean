import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModel
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModelReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic

/-!
# Actual minimal-model reduction for the source Psi integral model

From an actual integral model `M` over the adic completion integers, take the
actual base change `W`, the Mathlib minimal model `W.minimal R`, and its actual
Mathlib reduction `WeierstrassCurve.reduction R W.minimal`.  The resulting
reduced curve is identified coefficientwise with the residue-field reduction of
the chosen integral model; for the original model `M` the identification is
proved under the explicit chosen-integral-model and integral-change hypotheses.
No fake reduction is introduced.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.SourcePsiActualMinimalModelReduction

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual completion integer ring. -/
abbrev SourcePsiActualIntegers : Type u :=
  SourcePsiCompletionIntegers S v

/-- The actual completion field. -/
abbrev SourcePsiActualField : Type u :=
  SourcePsiCompletionField S v

/-- The actual residue field in which the reduction lives. -/
abbrev SourcePsiActualResidueField : Type u :=
  IsLocalRing.ResidueField (SourcePsiActualIntegers S v)

/-- The actual base change of an integral model to the completion field. -/
noncomputable def actualBaseChangeCurve
    (M : SourcePsiIntegralModelData S v) : WeierstrassCurve (SourcePsiActualField S v) :=
  M.curve.map (algebraMap (SourcePsiActualIntegers S v) (SourcePsiActualField S v))

theorem actualBaseChangeCurve_eq_source
    (M : SourcePsiIntegralModelData S v) :
    actualBaseChangeCurve S v M = SourcePsiBaseChangedCurve S v :=
  M.baseChange_eq

noncomputable instance actualBaseChangeCurve_isIntegral
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (actualBaseChangeCurve S v M) :=
  ⟨M.curve, rfl⟩

/-- The actual Mathlib minimal model of the base-changed curve. -/
noncomputable def actualMinimalModel
    (M : SourcePsiIntegralModelData S v) : WeierstrassCurve (SourcePsiActualField S v) :=
  (actualBaseChangeCurve S v M).minimal (SourcePsiActualIntegers S v)

/-- The actual variable change chosen by Mathlib's minimal-model construction. -/
noncomputable def actualMinimalChange
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve.VariableChange (SourcePsiActualField S v) :=
  (actualBaseChangeCurve S v M).exists_isMinimal (SourcePsiActualIntegers S v) |>.choose

theorem actualMinimalModel_eq_smul
    (M : SourcePsiIntegralModelData S v) :
    actualMinimalModel S v M =
      actualMinimalChange S v M • actualBaseChangeCurve S v M :=
  rfl

noncomputable instance actualMinimalModel_isMinimal
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve.IsMinimal (SourcePsiActualIntegers S v)
      (actualMinimalModel S v M) :=
  (actualBaseChangeCurve S v M).exists_isMinimal
    (SourcePsiActualIntegers S v) |>.choose_spec

/-- The actual integral model selected by Mathlib from the minimal model. -/
noncomputable def actualMinimalIntegralModel
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiActualIntegers S v) :=
  WeierstrassCurve.integralModel (SourcePsiActualIntegers S v)
    (actualMinimalModel S v M)

theorem actualMinimalIntegralModel_baseChange
    (M : SourcePsiIntegralModelData S v) :
    (actualMinimalIntegralModel S v M).map
        (algebraMap (SourcePsiActualIntegers S v) (SourcePsiActualField S v)) =
      actualMinimalModel S v M :=
  WeierstrassCurve.baseChange_integralModel_eq (R := SourcePsiActualIntegers S v)
    (actualMinimalModel S v M)

/-- The actual Mathlib reduced curve of the minimal model. -/
noncomputable def actualMinimalReduction
    (M : SourcePsiIntegralModelData S v) : WeierstrassCurve (SourcePsiActualResidueField S v) :=
  WeierstrassCurve.reduction (SourcePsiActualIntegers S v)
    (actualMinimalModel S v M)

theorem actualMinimalReduction_eq_map_integralModel
    (M : SourcePsiIntegralModelData S v) :
    actualMinimalReduction S v M =
      (actualMinimalIntegralModel S v M).map
        (IsLocalRing.residue (SourcePsiActualIntegers S v)) :=
  rfl

theorem actualMinimalReduction_a₁
    (M : SourcePsiIntegralModelData S v) :
    (actualMinimalReduction S v M).a₁ =
      IsLocalRing.residue (SourcePsiActualIntegers S v)
        (actualMinimalIntegralModel S v M).a₁ :=
  rfl

theorem actualMinimalReduction_a₂
    (M : SourcePsiIntegralModelData S v) :
    (actualMinimalReduction S v M).a₂ =
      IsLocalRing.residue (SourcePsiActualIntegers S v)
        (actualMinimalIntegralModel S v M).a₂ :=
  rfl

theorem actualMinimalReduction_a₃
    (M : SourcePsiIntegralModelData S v) :
    (actualMinimalReduction S v M).a₃ =
      IsLocalRing.residue (SourcePsiActualIntegers S v)
        (actualMinimalIntegralModel S v M).a₃ :=
  rfl

theorem actualMinimalReduction_a₄
    (M : SourcePsiIntegralModelData S v) :
    (actualMinimalReduction S v M).a₄ =
      IsLocalRing.residue (SourcePsiActualIntegers S v)
        (actualMinimalIntegralModel S v M).a₄ :=
  rfl

theorem actualMinimalReduction_a₆
    (M : SourcePsiIntegralModelData S v) :
    (actualMinimalReduction S v M).a₆ =
      IsLocalRing.residue (SourcePsiActualIntegers S v)
        (actualMinimalIntegralModel S v M).a₆ :=
  rfl

theorem actualMinimalReduction_coefficients
    (M : SourcePsiIntegralModelData S v) :
    (actualMinimalReduction S v M).a₁ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₁ ∧
      (actualMinimalReduction S v M).a₂ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₂ ∧
      (actualMinimalReduction S v M).a₃ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₃ ∧
      (actualMinimalReduction S v M).a₄ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₄ ∧
      (actualMinimalReduction S v M).a₆ =
        IsLocalRing.residue (SourcePsiActualIntegers S v)
          (actualMinimalIntegralModel S v M).a₆ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The actual selected integral model as a source integral model datum, when
its base change is the original base-changed curve.  This is the conditional
chosen-integral-model identification; no model equality is assumed globally. -/
structure ActualMinimalModelChoice where
  model : SourcePsiIntegralModelData S v
  integralModel_eq : actualMinimalIntegralModel S v model = model.curve

/-- The actual reduced curve of the original model, in the held `SourcePsiReducedCurve` API. -/
noncomputable def actualOriginalReducedCurve
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiActualResidueField S v) :=
  SourcePsiReducedCurve S v M

theorem actualOriginalReducedCurve_eq_coefficientReductions
    (M : SourcePsiIntegralModelData S v) :
    actualOriginalReducedCurve S v M =
      { a₁ := sourcePsiIntegralCoefficientReduction S v M.curve.a₁
        a₂ := sourcePsiIntegralCoefficientReduction S v M.curve.a₂
        a₃ := sourcePsiIntegralCoefficientReduction S v M.curve.a₃
        a₄ := sourcePsiIntegralCoefficientReduction S v M.curve.a₄
        a₆ := sourcePsiIntegralCoefficientReduction S v M.curve.a₆ } :=
  rfl

/-- Under the chosen-integral-model equality, the actual Mathlib minimal
reduction is the held `SourcePsiReducedCurve` of the chosen integral model. -/
theorem actualMinimalReduction_eq_sourcePsiReducedCurve_of_choice
    (D : ActualMinimalModelChoice S v) :
    actualMinimalReduction S v D.model =
      SourcePsiReducedCurve S v
        { curve := actualMinimalIntegralModel S v D.model
          baseChange_eq := D.model.baseChange_eq } :=
  by
  ext <;> simp [actualMinimalReduction, SourcePsiReducedCurve,
    sourcePsiIntegralCoefficientReduction, WeierstrassCurve.reduction]

theorem actualMinimalReduction_isResidueMap
    (M : SourcePsiIntegralModelData S v) :
    actualMinimalReduction S v M =
      (actualMinimalIntegralModel S v M).map
        (IsLocalRing.residue (SourcePsiActualIntegers S v)) :=
  rfl

/-- Special-fiber identification structure for the actual Mathlib reduction. -/
structure ActualMinimalReductionIdentification
    (M : SourcePsiIntegralModelData S v) where
  specialFiber : WeierstrassCurve (SourcePsiActualResidueField S v)
  specialFiber_eq :
    specialFiber = actualMinimalReduction S v M

noncomputable def actualMinimalReductionIdentification
    (M : SourcePsiIntegralModelData S v) :
    ActualMinimalReductionIdentification S v M where
  specialFiber := actualMinimalReduction S v M
  specialFiber_eq := rfl

theorem actualMinimalReductionIdentification_specialFiber_eq
    (M : SourcePsiIntegralModelData S v)
    (D : ActualMinimalReductionIdentification S v M) :
    D.specialFiber = actualMinimalReduction S v M :=
  D.specialFiber_eq

theorem actualMinimalReductionIdentification_reducedCurve_eq
    (M : SourcePsiIntegralModelData S v)
    (D : ActualMinimalReductionIdentification S v M) :
    D.specialFiber =
      (actualMinimalIntegralModel S v M).map
        (IsLocalRing.residue (SourcePsiActualIntegers S v)) :=
  by
  rw [D.specialFiber_eq]
  rfl

/-- The actual minimal model is a variable change of the actual base change. -/
theorem actualMinimalModel_isVariableChange
    (M : SourcePsiIntegralModelData S v) :
    ∃ C : WeierstrassCurve.VariableChange (SourcePsiActualField S v),
      actualMinimalModel S v M = C • actualBaseChangeCurve S v M :=
  ⟨actualMinimalChange S v M, actualMinimalModel_eq_smul S v M⟩

/-- The actual minimal model is integral (it is the chosen minimal integral
model). -/
theorem actualMinimalModel_isIntegral
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve.IsIntegral (SourcePsiActualIntegers S v)
      (actualMinimalModel S v M) :=
  inferInstance

/-- The actual reduction is an actual Weierstrass curve over the actual residue
field. -/
theorem actualMinimalReduction_type
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiActualResidueField S v) :=
  actualMinimalReduction S v M

/-- The actual residue-field reduction of the chosen integral model is the
held `SourcePsiReducedCurve`. -/
theorem actualResidueMap_eq_sourcePsiReducedCurve
    (M : SourcePsiIntegralModelData S v) :
    M.curve.map (IsLocalRing.residue (SourcePsiActualIntegers S v)) =
      SourcePsiReducedCurve S v M :=
  by
  ext <;> rfl

/-- The actual minimal reduction is identified with the residue reduction of
its selected integral model. -/
theorem actualMinimalReduction_identification
    (M : SourcePsiIntegralModelData S v) :
    actualMinimalReduction S v M =
      (actualMinimalIntegralModel S v M).map
        (IsLocalRing.residue (SourcePsiActualIntegers S v)) ∧
      (actualMinimalIntegralModel S v M).map
        (algebraMap (SourcePsiActualIntegers S v) (SourcePsiActualField S v)) =
      actualMinimalModel S v M :=
  ⟨rfl, actualMinimalIntegralModel_baseChange S v M⟩

end LeanFormal.IUT.SourcePsiActualMinimalModelReduction

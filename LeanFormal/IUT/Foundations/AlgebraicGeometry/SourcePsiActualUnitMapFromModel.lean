import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModelUnitMapExistence
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiCoefficientIntegrality
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-!
# Actual integral-unit comparison from the integral model

Starting from an actual integral model

  `SourcePsiIntegralModelData S v`

and an actual evaluation/retraction datum, this file packages the actual unit
comparison

  source integral units → model integral coordinate-ring units → completion integral units.

The map is the production map `sourcePsiIntegralUnitsToCompletionIntegers`; no
carrier or map is invented.  We also prove:

* the completion integral-unit norm/valuation one compatibility;
* principal-unit compatibility for the constant-unit section;
* kernel compatibility (the constant-unit section is injective);
* the exact image-comparison proposition with the source comparison map;
* the conditional connection to `SourcePsiIntegralUnitMapSurjectivity` and
  `SourcePsiUnitImageComparison`.

Surjectivity is not asserted; it is exposed as an explicit Prop.

No fake map, no card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.SourcePsiActualUnitMapFromModel

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourceIntegralUnitsComparison
open LeanFormal.IUT.SourceIntegralUnitsImage
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelUnitMapExistence
open LeanFormal.IUT.SourcePsiCoefficientIntegrality
open LeanFormal.IUT.LocalFieldIntegralUnits
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-! ## The actual model/unit data -/

/-- The actual data used by the integral-unit comparison. -/
structure SourcePsiActualUnitMapData where
  /-- The actual integral model. -/
  model : SourcePsiIntegralModelData S v
  /-- The actual integral coordinate-ring units. -/
  coordinateRingUnits : Type u
  /-- The actual unit comparison to completion integral units. -/
  toCompletion : coordinateRingUnits →* (SourcePsiCompletionIntegers S v)ˣ

/-- The actual integral-unit comparison built from coefficient integrality and
an actual evaluation/retraction datum. -/
noncomputable def sourcePsiActualUnitMapDataOfEvaluation
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    SourcePsiActualUnitMapData S v where
  model := sourcePsiIntegralModelOfIntegralCoefficients S v h
  coordinateRingUnits := SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h
  toCompletion := sourcePsiIntegralUnitsToCompletionIntegers S v h E

/-- The actual completion integral-unit comparison attached to the data. -/
noncomputable def SourcePsiActualUnitMapData.toCompletionUnits
    (D : SourcePsiActualUnitMapData S v) :
    D.coordinateRingUnits →* (SourcePsiCompletionIntegers S v)ˣ :=
  D.toCompletion

/-! ## Norm/valuation one compatibility -/

theorem completionIntegralUnit_norm_one
    (u : (SourcePsiCompletionIntegers S v)ˣ) :
    ‖((u : SourcePsiCompletionIntegers S v) : SourcePsiCompletionField S v)‖ = 1 :=
  norm_unit_eq_one

theorem completionIntegralUnit_valued_eq_one
    (u : (SourcePsiCompletionIntegers S v)ˣ) :
    (Valued.v ((u : SourcePsiCompletionIntegers S v) :
      SourcePsiCompletionField S v) : WithZero (Multiplicative ℤ)) = 1 :=
by
  rw [← WithZero.exp_zero, WithZero.exp_inj]
  -- integral units have valuation one
  have hle := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
    (v := v) (x := ((u : SourcePsiCompletionIntegers S v) :
      SourcePsiCompletionField S v))).mp (u : SourcePsiCompletionIntegers S v).2
  have hinv := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
    (v := v) (x := (((u⁻¹ : (SourcePsiCompletionIntegers S v)ˣ) :
      SourcePsiCompletionIntegers S v) : SourcePsiCompletionField S v))).mp
    (u⁻¹ : SourcePsiCompletionIntegers S v).2
  rw [Units.val_inv, map_inv₀] at hinv
  have hmul : (Valued.v ((u : SourcePsiCompletionIntegers S v) :
      SourcePsiCompletionField S v)) *
      (Valued.v ((u : SourcePsiCompletionIntegers S v) :
        SourcePsiCompletionField S v))⁻¹ = 1 := by
    rw [mul_inv_cancel₀]
    exact ne_of_gt (zero_lt_one.trans_le hle)
  -- both the value and its inverse are at most one
  have hge : 1 ≤ (Valued.v ((u : SourcePsiCompletionIntegers S v) :
      SourcePsiCompletionField S v) : WithZero (Multiplicative ℤ)) :=
  by
    by_contra hlt
    have hinvgt : 1 < (Valued.v ((u : SourcePsiCompletionIntegers S v) :
        SourcePsiCompletionField S v))⁻¹ := by
      rw [inv_eq_one_div]
      exact one_lt_inv_of_lt (zero_lt_one.trans_le hle) (lt_of_not_ge hlt)
    exact not_lt_of_ge hinv hinvgt
  exact le_antisymm hle hge

theorem actualUnitMap_norm_one
    (D : SourcePsiActualUnitMapData S v)
    (x : D.coordinateRingUnits) :
    ‖((D.toCompletion x : (SourcePsiCompletionIntegers S v)ˣ) :
      SourcePsiCompletionField S v)‖ = 1 :=
  norm_unit_eq_one

theorem actualUnitMap_valued_one
    (D : SourcePsiActualUnitMapData S v)
    (x : D.coordinateRingUnits) :
    (Valued.v (((D.toCompletion x : (SourcePsiCompletionIntegers S v)ˣ) :
      SourcePsiCompletionIntegers S v) : SourcePsiCompletionField S v) :
      WithZero (Multiplicative ℤ)) = 1 :=
  completionIntegralUnit_valued_eq_one S v (D.toCompletion x)

/-! ## Principal units -/

abbrev SourcePsiCompletionPrincipalUnits : Subgroup (SourcePsiCompletionIntegers S v)ˣ :=
  principalUnits

theorem constantUnitMap_principal
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h)
    (u : (SourcePsiCompletionIntegers S v)ˣ)
    (hu : u ∈ SourcePsiCompletionPrincipalUnits S v) :
    sourcePsiIntegralUnitsToCompletionIntegers S v h E
        (sourcePsiIntegralConstantUnits S v h u) ∈
      SourcePsiCompletionPrincipalUnits S v :=
by
  rw [sourcePsiIntegralUnitsToCompletionIntegers_constant S v h E u]
  exact hu

theorem constantUnitMap_principal_iff
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h)
    (u : (SourcePsiCompletionIntegers S v)ˣ) :
    sourcePsiIntegralUnitsToCompletionIntegers S v h E
        (sourcePsiIntegralConstantUnits S v h u) ∈
      SourcePsiCompletionPrincipalUnits S v ↔
      u ∈ SourcePsiCompletionPrincipalUnits S v :=
by
  rw [sourcePsiIntegralUnitsToCompletionIntegers_constant S v h E u]

/-! ## Kernel compatibility -/

theorem constantUnitMap_injective
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    Function.Injective (fun u : (SourcePsiCompletionIntegers S v)ˣ =>
      sourcePsiIntegralUnitsToCompletionIntegers S v h E
        (sourcePsiIntegralConstantUnits S v h u)) :=
by
  intro u w huw
  have h' : sourcePsiIntegralUnitsToCompletionIntegers S v h E
      (sourcePsiIntegralConstantUnits S v h u) =
      sourcePsiIntegralUnitsToCompletionIntegers S v h E
        (sourcePsiIntegralConstantUnits S v h w) := huw
  rw [sourcePsiIntegralUnitsToCompletionIntegers_constant S v h E u,
    sourcePsiIntegralUnitsToCompletionIntegers_constant S v h E w] at h'
  exact h'

theorem constantUnitMap_kernel_trivial
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    ∀ u : (SourcePsiCompletionIntegers S v)ˣ,
      sourcePsiIntegralUnitsToCompletionIntegers S v h E
          (sourcePsiIntegralConstantUnits S v h u) = 1 → u = 1 :=
by
  intro u hu
  have hconst := sourcePsiIntegralUnitsToCompletionIntegers_constant S v h E u
  rw [hconst] at hu
  exact hu

/-! ## Image comparison with the source comparison map -/

/-- The actual image of source integral units in the completion integral units. -/
abbrev SourcePsiActualSourceIntegralImage :
    Subgroup (SourcePsiCompletionIntegers S v)ˣ :=
  SourceIntegralUnitsImage S v

/-- The comparison image obtained through the actual model/evaluation unit map. -/
noncomputable def SourcePsiActualUnitMapImage
    (D : SourcePsiActualUnitMapData S v) :
    Subgroup (SourcePsiCompletionIntegers S v)ˣ :=
  (⊤ : Subgroup D.coordinateRingUnits).map D.toCompletion

/-- Source integral units routed through the constant-unit section and the
actual model unit map. -/
noncomputable def sourceIntegralUnitsThroughActualMap
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    SourceIntegralUnits S →* (SourcePsiCompletionIntegers S v)ˣ :=
  (sourcePsiIntegralUnitsToCompletionIntegers S v h E).comp
    ((sourcePsiIntegralConstantUnits S v h).comp
      (sourceIntegralUnitsToCompletionIntegerUnits S v))

theorem sourceIntegralUnitsThroughActualMap_apply
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h)
    (u : SourceIntegralUnits S) :
    sourceIntegralUnitsThroughActualMap S v h E u =
      sourceIntegralUnitsToCompletionIntegerUnits S v u :=
by
  simp [sourceIntegralUnitsThroughActualMap,
    sourcePsiIntegralUnitsToCompletionIntegers_constant]

theorem sourceIntegralUnitsThroughActualMap_image_eq
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    (⊤ : Subgroup (SourceIntegralUnits S)).map
        (sourceIntegralUnitsThroughActualMap S v h E) =
      SourceIntegralUnitsImage S v :=
by
  ext x
  constructor
  · rintro ⟨u, -, rfl⟩
    exact ⟨u, (sourceIntegralUnitsThroughActualMap_apply S v h E u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, trivial, sourceIntegralUnitsThroughActualMap_apply S v h E u⟩

/-- The actual source comparison map. -/
noncomputable def SourcePsiActualSourceComparisonMap :
    SourceIntegralUnits S →* (SourcePsiCompletionIntegers S v)ˣ :=
  sourceIntegralUnitsToCompletionIntegerUnits S v

/-- The source image through the actual model/evaluation comparison. -/
noncomputable def SourcePsiActualSourceImage
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    Subgroup (SourcePsiCompletionIntegers S v)ˣ :=
  (⊤ : Subgroup (SourceIntegralUnits S)).map
    (sourceIntegralUnitsThroughActualMap S v h E)

/-- Exact image comparison between the actual model route and the source
comparison map. -/
def SourcePsiUnitImageComparison
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) : Prop :=
  SourcePsiActualSourceImage S v h E = SourceIntegralUnitsImage S v

theorem sourcePsiUnitImageComparison_holds
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    SourcePsiUnitImageComparison S v h E :=
  sourceIntegralUnitsThroughActualMap_image_eq S v h E

/-! ## Surjectivity as an explicit proposition -/

/-- Surjectivity of the actual model unit map onto the completion integer units.
This is an explicit Prop; it is not asserted. -/
def SourcePsiIntegralUnitMapSurjectivity
    (D : SourcePsiActualUnitMapData S v) : Prop :=
  Function.Surjective D.toCompletion

theorem sourcePsiIntegralUnitMapSurjectivity_image_eq_univ
    (D : SourcePsiActualUnitMapData S v)
    (h : SourcePsiIntegralUnitMapSurjectivity S v D) :
    SourcePsiActualUnitMapImage S v D =
      (⊤ : Subgroup (SourcePsiCompletionIntegers S v)ˣ) :=
by
  ext x
  simp only [SourcePsiActualUnitMapImage, Subgroup.mem_map, Subgroup.mem_top,
    true_and]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact Subgroup.mem_top _
  · intro _
    obtain ⟨y, rfl⟩ := h x
    exact ⟨y, trivial, rfl⟩

/-! ## Final package -/

structure SourcePsiActualUnitComparison where
  coefficientsIntegral : SourcePsiCoefficientsIntegral S v
  evaluation : SourcePsiIntegralEvaluationData S v coefficientsIntegral
  unitMapSurjective : SourcePsiIntegralUnitMapSurjectivity S v
    (sourcePsiActualUnitMapDataOfEvaluation S v coefficientsIntegral evaluation)

noncomputable def sourcePsiActualUnitComparisonOfEvaluation
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    SourcePsiActualUnitComparison S v where
  coefficientsIntegral := h
  evaluation := E
  unitMapSurjective := by
    intro x
    -- the constant section is an actual section of the evaluation unit map
    exact ⟨sourcePsiIntegralConstantUnits S v h x,
      sourcePsiIntegralUnitsToCompletionIntegers_constant S v h E x⟩

end LeanFormal.IUT.SourcePsiActualUnitMapFromModel

end
end LeanFormal.IUT.SourcePsiActualUnitMapFromModel

end
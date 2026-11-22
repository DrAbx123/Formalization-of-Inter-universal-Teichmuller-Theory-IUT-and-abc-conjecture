/-
  Existence of the integral-model unit map, under the exact five coefficient
  integrality conditions, and its compatibility with the base-change route.

  Coefficient integrality constructs the actual raw integral model and the actual
  integral coordinate ring.  The natural unit map from the base adic completion
  integers into the integral coordinate-ring units is the constant-unit map.
  A map in the opposite direction (integral coordinate-ring units -> completion
  integer units) exists under an explicit actual evaluation/retraction datum;
  coefficient integrality alone does not supply one.  The exact evaluation
  residual is stated, with no fake carrier or spec alias.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiCoefficientIntegrality
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiIntegralModelUnitMapExistence

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourceIntegralUnitsComparison
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelReduction
open LeanFormal.IUT.SourcePsiCoefficientIntegrality
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- Under the exact five coefficient integrality conditions, the actual raw
integral model over the adic completion integers. -/
noncomputable def sourcePsiIntegralModelOfIntegralCoefficients
    (h : SourcePsiCoefficientsIntegral S v) :
    SourcePsiIntegralModelData S v :=
  sourcePsiIntegralModelDataOfCoefficients S v h

/-- Under coefficient integrality, the actual integral coordinate ring. -/
abbrev SourcePsiIntegralCoordinateRingOfCoefficients
    (h : SourcePsiCoefficientsIntegral S v) : Type u :=
  SourcePsiIntegralCoordinateRing S v
    (sourcePsiIntegralModelOfIntegralCoefficients S v h)

/-- The actual unit group of the integral coordinate ring built from coefficient
integrality. -/
abbrev SourcePsiIntegralCoordinateRingUnitsOfCoefficients
    (h : SourcePsiCoefficientsIntegral S v) : Type u :=
  (SourcePsiIntegralCoordinateRingOfCoefficients S v h)ˣ

/-- The actual completion integer units. -/
abbrev SourcePsiCompletionIntegerUnits : Type u :=
  CompletionIntegralUnits S v

/-- The actual source integral-unit comparison into the completion integer units. -/
noncomputable def sourceIntegralUnitsToCompletionIntegerUnits :
    SourceIntegralUnits S →* SourcePsiCompletionIntegerUnits S v :=
  sourceIntegralUnitsToCompletion S v

/-- The constant-unit map from the actual adic completion integers into the
actual integral coordinate-ring units. -/
noncomputable def sourcePsiIntegralConstantUnits
    (h : SourcePsiCoefficientsIntegral S v) :
    (SourcePsiCompletionIntegers S v)ˣ →*
      SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h :=
  Units.map (algebraMap (SourcePsiCompletionIntegers S v)
    (SourcePsiIntegralCoordinateRingOfCoefficients S v h)).toMonoidHom

theorem sourcePsiIntegralConstantUnits_mul
    (h : SourcePsiCoefficientsIntegral S v)
    (x y : (SourcePsiCompletionIntegers S v)ˣ) :
    sourcePsiIntegralConstantUnits S v h (x * y) =
      sourcePsiIntegralConstantUnits S v h x *
        sourcePsiIntegralConstantUnits S v h y :=
  map_mul (sourcePsiIntegralConstantUnits S v h) x y

theorem sourcePsiIntegralConstantUnits_one
    (h : SourcePsiCoefficientsIntegral S v) :
    sourcePsiIntegralConstantUnits S v h
        (1 : (SourcePsiCompletionIntegers S v)ˣ) = 1 :=
  map_one (sourcePsiIntegralConstantUnits S v h)

/-- The constant units, followed by the actual base-change unit map, are the
algebraic images in the base-changed coordinate-ring units. -/
theorem sourcePsiIntegralConstantUnits_baseChange
    (h : SourcePsiCoefficientsIntegral S v)
    (u : (SourcePsiCompletionIntegers S v)ˣ) :
    sourcePsiIntegralUnitsToBaseChangeUnits S v
        (sourcePsiIntegralModelOfIntegralCoefficients S v h)
        (sourcePsiIntegralConstantUnits S v h u) =
      Units.map (algebraMap S.arithmetic.F
        (SourcePsiCompletionCoordinateRing S v)).toMonoidHom
        (Units.map (algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiCompletionField S v)).toMonoidHom u) := by
  ext
  simp [sourcePsiIntegralConstantUnits,
    sourcePsiIntegralUnitsToBaseChangeUnits,
    SourcePsiIntegralCoordinateRingOfCoefficients,
    SourcePsiIntegralCoordinateRing,
    SourcePsiIntegralCoordinateRingOfCoefficients
    ]

/-- Compatibility of the actual source integral-unit route with the constant-unit
route into the base-changed coordinate ring. -/
theorem sourceIntegralUnitsToCompletionCoordinateRing_compat
    (h : SourcePsiCoefficientsIntegral S v) (u : SourceIntegralUnits S) :
    sourcePsiIntegralUnitsToBaseChangeUnits S v
        (sourcePsiIntegralModelOfIntegralCoefficients S v h)
        (sourcePsiIntegralConstantUnits S v h
          (sourceIntegralUnitsToCompletionIntegerUnits S v u)) =
      sourceIntegralUnitsToCompletionCoordinateRing S v u := by
  ext
  simp [sourcePsiIntegralConstantUnits,
    sourcePsiIntegralUnitsToBaseChangeUnits,
    sourceIntegralUnitsToCompletionIntegerUnits,
    sourceIntegralUnitsToCompletionCoordinateRing,
    sourceIntegralUnitsToCompletion,
    sourceIntegralUnitsToPsiUnits]

/-- An actual evaluation/retraction of the integral coordinate ring onto the
adic completion integers.  This is the exact extra datum needed for a unit map
in the opposite direction. -/
structure SourcePsiIntegralEvaluationData
    (h : SourcePsiCoefficientsIntegral S v) where
  /-- The actual ring-hom evaluation/retraction. -/
  evaluation : SourcePsiIntegralCoordinateRingOfCoefficients S v h →+*
    SourcePsiCompletionIntegers S v
  /-- It is a retraction of the actual constant algebra map. -/
  evaluation_algebraMap :
    evaluation.comp (algebraMap (SourcePsiCompletionIntegers S v)
      (SourcePsiIntegralCoordinateRingOfCoefficients S v h)) =
      RingHom.id (SourcePsiCompletionIntegers S v)

/-- Under an actual evaluation datum, the induced unit map from the integral
coordinate-ring units to the completion integer units. -/
noncomputable def sourcePsiIntegralUnitsToCompletionIntegers
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h →*
      (SourcePsiCompletionIntegers S v)ˣ :=
  Units.map E.evaluation.toMonoidHom

/-- The induced unit map retracts the constant-unit map. -/
theorem sourcePsiIntegralUnitsToCompletionIntegers_constant
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h)
    (u : (SourcePsiCompletionIntegers S v)ˣ) :
    sourcePsiIntegralUnitsToCompletionIntegers S v h E
        (sourcePsiIntegralConstantUnits S v h u) = u := by
  ext
  have hret := congrFun (congrArg DFunLike.coe E.evaluation_algebraMap) (u : SourcePsiCompletionIntegers S v)
  simpa [sourcePsiIntegralUnitsToCompletionIntegers,
    sourcePsiIntegralConstantUnits] using hret

/-- Under an actual evaluation datum, the requested unit map exists and is
compatible with the source integral-unit comparison. -/
theorem sourcePsiIntegralUnitMap_compat
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h)
    (u : SourceIntegralUnits S) :
    sourcePsiIntegralUnitsToCompletionIntegers S v h E
        (sourcePsiIntegralConstantUnits S v h
          (sourceIntegralUnitsToCompletionIntegerUnits S v u)) =
      sourceIntegralUnitsToCompletionIntegerUnits S v u := by
  exact sourcePsiIntegralUnitsToCompletionIntegers_constant S v h E _

/-! ## Exact existence statement and residual

Coefficient integrality constructs the actual integral model and the actual
integral coordinate ring.  The constant-unit map

  (v.adicCompletionIntegers F)^× -> (integral coordinate ring)^×

is actual and compatible with the base-change route.  A unit map

  (integral coordinate ring)^× -> (v.adicCompletionIntegers F)^×

is constructed only from an actual evaluation/retraction datum
`SourcePsiIntegralEvaluationData`.  Coefficient integrality alone does not supply
such an evaluation: the affine coordinate ring is not canonically a constant
ring, and no integral source point/evaluation is constructed by the coefficient
conditions.

Exact missing object: an actual retraction/evaluation of the integral coordinate
ring onto the adic completion integers, or an actual proof that all units of the
integral coordinate ring are constant (which would give the inverse of the
constant-unit map).  Both are arithmetic/geometric source statements, not cards.

The previous `SourcePsiIntegralModelUnitMapData` residual is therefore refined:
its `toCompletion` field exists under `SourcePsiIntegralEvaluationData`; its
`sourceToModel` field still requires an actual source-integral-unit map into the
integral coordinate ring, which coefficient integrality alone does not provide.
-/


/-! ## Map laws and conditional existence

theorem sourcePsiIntegralUnitsToCompletionIntegers_one
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h) :
    sourcePsiIntegralUnitsToCompletionIntegers S v h E
        (1 : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) = 1 :=
  map_one (sourcePsiIntegralUnitsToCompletionIntegers S v h E)

theorem sourcePsiIntegralUnitsToCompletionIntegers_mul
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h)
    (x y : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) :
    sourcePsiIntegralUnitsToCompletionIntegers S v h E (x * y) =
      sourcePsiIntegralUnitsToCompletionIntegers S v h E x *
        sourcePsiIntegralUnitsToCompletionIntegers S v h E y :=
  map_mul (sourcePsiIntegralUnitsToCompletionIntegers S v h E) x y

theorem sourcePsiIntegralUnitsToCompletionIntegers_inv
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h)
    (x : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) :
    sourcePsiIntegralUnitsToCompletionIntegers S v h E x⁻¹ =
      (sourcePsiIntegralUnitsToCompletionIntegers S v h E x)⁻¹ :=
  map_inv (sourcePsiIntegralUnitsToCompletionIntegers S v h E) x

/-- On constant units the evaluation retraction acts as the identity. -/
theorem sourcePsiIntegralEvaluationData_apply_constant
    (h : SourcePsiCoefficientsIntegral S v)
    (E : SourcePsiIntegralEvaluationData S v h)
    (r : SourcePsiCompletionIntegers S v) :
    E.evaluation (algebraMap (SourcePsiCompletionIntegers S v)
      (SourcePsiIntegralCoordinateRingOfCoefficients S v h) r) = r := by
  have hret := congrFun (congrArg DFunLike.coe E.evaluation_algebraMap) r
  simpa using hret

/-- Conditional existence package: the actual integral model, its coordinate
ring, and the evaluation/retraction datum.  This is a data structure, not an
inhabitant of the residual. -/
structure SourcePsiIntegralUnitMapExistenceData where
  coefficientsIntegral : SourcePsiCoefficientsIntegral S v
  evaluation : SourcePsiIntegralEvaluationData S v coefficientsIntegral

/-- The exact conditional existence Proposition. -/
def SourcePsiIntegralUnitMapExistence : Prop :=
  Nonempty (SourcePsiIntegralUnitMapExistenceData S v)

/-- A unit-map existence datum exposes an actual integral unit map. -/
noncomputable def SourcePsiIntegralUnitMapExistenceData.toCompletion
    (D : SourcePsiIntegralUnitMapExistenceData S v) :
    SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v D.coefficientsIntegral →*
      (SourcePsiCompletionIntegers S v)ˣ :=
  sourcePsiIntegralUnitsToCompletionIntegers S v D.coefficientsIntegral D.evaluation

/-- The conditional existence datum is not constructed unconditionally. -/
theorem SourcePsiIntegralUnitMapExistence_requires_evaluation
    (D : SourcePsiIntegralUnitMapExistenceData S v) :
    Nonempty (SourcePsiIntegralEvaluationData S v D.coefficientsIntegral) :=
  ⟨D.evaluation⟩

/-! ## Exact missing evaluation/retraction

The only missing datum for the requested opposite unit map is the actual
evaluation/retraction `SourcePsiIntegralEvaluationData`.  It is a genuine ring
map from the integral coordinate ring to the adic completion integers that
retracts the actual constant algebra map.

Coefficient integrality constructs the integral coordinate ring but not such an
evaluation.  An actual source point with integral coordinates or a proof that all
units are constant would supply it; neither is constructed here.

This is a real arithmetic/geometric gap, not an alias or a card.

end LeanFormal.IUT.SourcePsiIntegralModelUnitMapExistence

end
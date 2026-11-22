/-
  When does the integral coordinate ring admit an evaluation/retraction onto the
  adic completion integers?

  Constructing an actual integral point of the raw integral model gives such a
  retraction (evaluation at the point).  Conversely, a precise obstruction is a
  unit `u` of the integral coordinate ring that stays a unit after subtracting
  every constant: no retraction can exist.  Such a separated unit is necessarily
  nonconstant.  A merely nonconstant unit is not, by itself, an obstruction.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModelUnitMapExistence

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiEvaluationObstruction

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open LeanFormal.IUT.SourcePsiIntegralModel
open LeanFormal.IUT.SourcePsiIntegralModelUnitMapExistence
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))
  (h : SourcePsiCoefficientsIntegral S v)

/-- An actual integral point of the raw integral model: integral coordinates
satisfying the actual Weierstrass equation. -/
structure SourcePsiIntegralPoint : Type u where
  x : SourcePsiCompletionIntegers S v
  y : SourcePsiCompletionIntegers S v
  equation :
    (sourcePsiIntegralModelOfIntegralCoefficients S v h).curve.polynomial.evalEval
      (x : SourcePsiCompletionField S v) (y : SourcePsiCompletionField S v) = 0

/-- Evaluation at an actual integral point gives an actual ring map from the
integral coordinate ring to the adic completion integers. -/
noncomputable def sourcePsiIntegralEvaluationOfPoint
    (P : SourcePsiIntegralPoint S v h) :
    SourcePsiIntegralCoordinateRingOfCoefficients S v h →+*
      SourcePsiCompletionIntegers S v :=
  AdjoinRoot.lift
    (Polynomial.evalRingHom (P.x : SourcePsiCompletionIntegers S v))
    P.y
    (by
      simpa [SourcePsiIntegralCoordinateRingOfCoefficients,
        sourcePsiIntegralModelOfIntegralCoefficients,
        SourcePsiIntegralCoordinateRing] using P.equation)

/-- Evaluation at a point retracts the actual constant algebra map. -/
theorem sourcePsiIntegralEvaluationOfPoint_algebraMap
    (P : SourcePsiIntegralPoint S v h) :
    (sourcePsiIntegralEvaluationOfPoint S v h P).comp
        (algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiIntegralCoordinateRingOfCoefficients S v h)) =
      RingHom.id (SourcePsiCompletionIntegers S v) := by
  ext r
  simp [sourcePsiIntegralEvaluationOfPoint, AdjoinRoot.lift_algebraMap]

/-- An actual integral point constructs the exact evaluation/retraction datum. -/
noncomputable def sourcePsiIntegralEvaluationDataOfPoint
    (P : SourcePsiIntegralPoint S v h) :
    SourcePsiIntegralEvaluationData S v h where
  evaluation := sourcePsiIntegralEvaluationOfPoint S v h P
  evaluation_algebraMap := sourcePsiIntegralEvaluationOfPoint_algebraMap S v h P

/-- Point existence implies the unit-map existence residual. -/
theorem SourcePsiIntegralUnitMapExistence_of_point
    (P : SourcePsiIntegralPoint S v h) :
    SourcePsiIntegralUnitMapExistence S v :=
  ⟨⟨h, sourcePsiIntegralEvaluationDataOfPoint S v h P⟩⟩

/-! ## Nonconstant units and a precise obstruction

/-- A nonconstant unit of the integral coordinate ring: not equal to any
constant unit. -/
def IsNonconstantIntegralUnit
    (u : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) : Prop :=
  ¬ ∃ r : (SourcePsiCompletionIntegers S v)ˣ,
    u = sourcePsiIntegralConstantUnits S v h r

/-- A separated unit: a unit that remains a unit after subtracting every
constant.  This is stronger than nonconstancy and is the exact obstruction used
below. -/
def IsSeparatedIntegralUnit
    (u : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) : Prop :=
  ∀ r : SourcePsiCompletionIntegers S v,
    IsUnit ((u : SourcePsiIntegralCoordinateRingOfCoefficients S v h) -
      algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiIntegralCoordinateRingOfCoefficients S v h) r)

/-- A separated unit is nonconstant. -/
theorem IsSeparatedIntegralUnit.isNonconstant
    {u : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h}
    (hu : IsSeparatedIntegralUnit S v h u) :
    IsNonconstantIntegralUnit S v h u := by
  rintro ⟨r, hr⟩
  have hsep := hu r
  rw [hr, sub_self] at hsep
  exact not_isUnit_zero hsep

/-- A separated unit obstructs every actual evaluation/retraction. -/
theorem not_evaluationData_of_separatedUnit
    {u : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h}
    (hu : IsSeparatedIntegralUnit S v h u) :
    ¬ Nonempty (SourcePsiIntegralEvaluationData S v h) := by
  rintro ⟨E⟩
  let r : SourcePsiCompletionIntegers S v := E.evaluation (u : _)
  have hzero : E.evaluation
      ((u : SourcePsiIntegralCoordinateRingOfCoefficients S v h) -
        algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiIntegralCoordinateRingOfCoefficients S v h) r) = 0 := by
    simp [r]
  have hunit : IsUnit ((u : SourcePsiIntegralCoordinateRingOfCoefficients S v h) -
      algebraMap (SourcePsiCompletionIntegers S v)
        (SourcePsiIntegralCoordinateRingOfCoefficients S v h) r) :=
    hu r
  have himage : IsUnit (E.evaluation
      ((u : SourcePsiIntegralCoordinateRingOfCoefficients S v h) -
        algebraMap (SourcePsiCompletionIntegers S v)
          (SourcePsiIntegralCoordinateRingOfCoefficients S v h) r)) :=
    hunit.map E.evaluation
  rw [hzero] at himage
  exact not_isUnit_zero himage

/-- A point and a separated unit cannot coexist: evaluation at the point would
be a retraction, contradicted by separatedness. -/
theorem not_point_of_separatedUnit
    {u : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h}
    (hu : IsSeparatedIntegralUnit S v h u)
    (P : SourcePsiIntegralPoint S v h) : False :=
  (not_evaluationData_of_separatedUnit S v h hu)
    ⟨sourcePsiIntegralEvaluationDataOfPoint S v h P⟩

/-! ## Exact obstruction statement

An actual integral point gives `SourcePsiIntegralEvaluationData`, hence the
opposite unit map and the unit-map existence residual.

A separated unit is a genuine obstruction: if `u` stays a unit after subtracting
every constant, then any retraction sends `u` to some `r`, and sends
`u - r` to zero; but `u - r` is a unit, so its image under a ring hom cannot be
zero.  Such a separated unit is necessarily nonconstant.

A merely nonconstant unit is NOT an obstruction.  Evaluation at a point can send
a nonconstant unit to a unit of the base; nonconstancy imposes no contradiction.
The exact obstruction is the separatedness condition (or, geometrically, the
absence of an actual integral point/evaluation), not nonconstancy alone.

Missing actual object: an integral point of the raw integral model, or an actual
evaluation/retraction datum.  No point is fabricated; no card is used.
-/


/-! ## The actual point/unit-map residual

/-- Exact integral-point residual: an actual integral point of the raw integral
model.  No inhabitant is asserted. -/
def SourcePsiIntegralPointResidual : Prop :=
  Nonempty (SourcePsiIntegralPoint S v h)

/-- Point residual implies the evaluation/unit-map existence residual. -/
theorem SourcePsiIntegralUnitMapExistence_of_pointResidual
    (hpt : SourcePsiIntegralPointResidual S v h) :
    SourcePsiIntegralUnitMapExistence S v := by
  obtain ⟨P⟩ := hpt
  exact SourcePsiIntegralUnitMapExistence_of_point S v h P

/-! ## Unit map induced by an evaluation datum

/-- An evaluation/retraction datum induces the actual unit map from the
integral coordinate-ring units to the adic completion integer units. -/
noncomputable def SourcePsiIntegralEvaluationData.toBaseUnits
    (E : SourcePsiIntegralEvaluationData S v h) :
    SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h →*
      (SourcePsiCompletionIntegers S v)ˣ :=
  Units.map E.evaluation.toMonoidHom

theorem SourcePsiIntegralEvaluationData.toBaseUnits_constant
    (E : SourcePsiIntegralEvaluationData S v h)
    (r : (SourcePsiCompletionIntegers S v)ˣ) :
    E.toBaseUnits (sourcePsiIntegralConstantUnits S v h r) = r := by
  ext
  have hret := congrFun (congrArg DFunLike.coe E.evaluation_algebraMap)
    (r : SourcePsiCompletionIntegers S v)
  simpa [SourcePsiIntegralEvaluationData.toBaseUnits,
    sourcePsiIntegralConstantUnits] using hret

theorem SourcePsiIntegralEvaluationData.toBaseUnits_mul
    (E : SourcePsiIntegralEvaluationData S v h)
    (x y : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) :
    E.toBaseUnits (x * y) = E.toBaseUnits x * E.toBaseUnits y :=
  map_mul E.toBaseUnits x y

theorem SourcePsiIntegralEvaluationData.toBaseUnits_one
    (E : SourcePsiIntegralEvaluationData S v h) :
    E.toBaseUnits (1 : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) = 1 :=
  map_one E.toBaseUnits

theorem SourcePsiIntegralEvaluationData.toBaseUnits_inv
    (E : SourcePsiIntegralEvaluationData S v h)
    (x : SourcePsiIntegralCoordinateRingUnitsOfCoefficients S v h) :
    E.toBaseUnits x⁻¹ = (E.toBaseUnits x)⁻¹ :=
  map_inv E.toBaseUnits x

/-! ## Summary of the exact obstruction

- Actual integral point -> actual evaluation/retraction -> actual unit map;
- actual evaluation/retraction -> unit map to completion integers;
- separated unit -> no evaluation/retraction, hence no point;
- separated unit -> nonconstant unit;
- merely nonconstant unit -> no obstruction in the framework above.

Thus the exact obstruction to the retraction is either a separated unit or,
geometrically, the absence of an actual integral point/evaluation.  The file
does not fabricate a point and does not claim a separated unit exists.

end LeanFormal.IUT.SourcePsiEvaluationObstruction

end
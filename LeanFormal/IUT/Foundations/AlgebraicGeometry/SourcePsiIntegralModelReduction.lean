/-
  Conditional reduction data for an actual integral model.

  Given `M : SourcePsiIntegralModelData`, the five coefficients live in the
  actual adic completion integers.  This file constructs their actual reductions
  in the residue field and the resulting reduced Weierstrass curve.  It does not
  identify that curve with an actual source special fiber and does not assert a
  proper regular model; those are exact residuals.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralModel

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiIntegralModelReduction

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourcePsiIntegralModel
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual residue field of the adic completion integers. -/
abbrev SourcePsiResidueField : Type u :=
  IsLocalRing.ResidueField (SourcePsiCompletionIntegers S v)

/-- Reduction of an actual completion integer to the residue field. -/
noncomputable def sourcePsiIntegralCoefficientReduction
    (a : SourcePsiCompletionIntegers S v) : SourcePsiResidueField S v :=
  IsLocalRing.residue (SourcePsiCompletionIntegers S v) a

/-- The actual reduced Weierstrass curve of an integral model. -/
noncomputable def SourcePsiReducedCurve
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiResidueField S v) where
  a₁ := sourcePsiIntegralCoefficientReduction S v M.curve.a₁
  a₂ := sourcePsiIntegralCoefficientReduction S v M.curve.a₂
  a₃ := sourcePsiIntegralCoefficientReduction S v M.curve.a₃
  a₄ := sourcePsiIntegralCoefficientReduction S v M.curve.a₄
  a₆ := sourcePsiIntegralCoefficientReduction S v M.curve.a₆

theorem SourcePsiReducedCurve_a₁ (M : SourcePsiIntegralModelData S v) :
    (SourcePsiReducedCurve S v M).a₁ =
      sourcePsiIntegralCoefficientReduction S v M.curve.a₁ := rfl

theorem SourcePsiReducedCurve_a₂ (M : SourcePsiIntegralModelData S v) :
    (SourcePsiReducedCurve S v M).a₂ =
      sourcePsiIntegralCoefficientReduction S v M.curve.a₂ := rfl

theorem SourcePsiReducedCurve_a₃ (M : SourcePsiIntegralModelData S v) :
    (SourcePsiReducedCurve S v M).a₃ =
      sourcePsiIntegralCoefficientReduction S v M.curve.a₃ := rfl

theorem SourcePsiReducedCurve_a₄ (M : SourcePsiIntegralModelData S v) :
    (SourcePsiReducedCurve S v M).a₄ =
      sourcePsiIntegralCoefficientReduction S v M.curve.a₄ := rfl

theorem SourcePsiReducedCurve_a₆ (M : SourcePsiIntegralModelData S v) :
    (SourcePsiReducedCurve S v M).a₆ =
      sourcePsiIntegralCoefficientReduction S v M.curve.a₆ := rfl

/-- Exact missing identification of the reduced curve with an actual source
special fiber.  The fields are actual data; no inhabitant is asserted. -/
structure SourcePsiReductionIdentification
    (M : SourcePsiIntegralModelData S v) where
  /-- The actual reduced curve is the claimed special fiber. -/
  specialFiber_eq : WeierstrassCurve (SourcePsiResidueField S v)
  /-- The claimed special fiber equals the constructed reduction. -/
  specialFiber_eq_reduced : specialFiber_eq = SourcePsiReducedCurve S v M

/-- Exact reduction residual: a model plus identification with the actual
source special fiber. -/
def SourcePsiReductionResidual : Prop :=
  ∃ M : SourcePsiIntegralModelData S v,
    Nonempty (SourcePsiReductionIdentification S v M)

/-- A reduction identification exposes its actual special-fiber equality. -/
theorem SourcePsiReductionIdentification_specialFiber_eq
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiReductionIdentification S v M) :
    D.specialFiber_eq = SourcePsiReducedCurve S v M := D.specialFiber_eq_reduced

/-! ## Exact missing reduction data

Constructed conditionally from `M`:
* the actual residue field of the adic completion integers;
* the actual coefficient reduction map;
* the actual reduced Weierstrass curve.

NOT constructed or claimed:
1. an actual integral model `M`;
2. a proof that the reduced curve is proper/regular or has the source reduction
   type;
3. an identification of the reduced curve with the actual source special fiber;
4. the actual component/node structure of the special fiber;
5. any source Psi^cns object.

The identification structure is actual data, not a fake source object.  It is
taken as an explicit hypothesis by the residual Proposition.

/-! ## Interface checklist

#check SourcePsiResidueField
#check sourcePsiIntegralCoefficientReduction
#check SourcePsiReducedCurve
#check SourcePsiReductionIdentification
#check SourcePsiReductionResidual
#check SourcePsiReductionIdentification_specialFiber_eq

/-! ## Batch metadata

- Batch: actual source integral model reduction.
- No compile in this drafting pass; no lean/lake invocation.
- Imports frozen: SourcePsiIntegralModel.
- Residual: actual model, proper/regular/source special-fiber identification;
  no fake reduction object.

/-! ## Reduced-curve API details

theorem SourcePsiReducedCurve_coefficients
    (M : SourcePsiIntegralModelData S v) :
    (SourcePsiReducedCurve S v M).a₁ = sourcePsiIntegralCoefficientReduction S v M.curve.a₁ ∧
    (SourcePsiReducedCurve S v M).a₂ = sourcePsiIntegralCoefficientReduction S v M.curve.a₂ ∧
    (SourcePsiReducedCurve S v M).a₃ = sourcePsiIntegralCoefficientReduction S v M.curve.a₃ ∧
    (SourcePsiReducedCurve S v M).a₄ = sourcePsiIntegralCoefficientReduction S v M.curve.a₄ ∧
    (SourcePsiReducedCurve S v M).a₆ = sourcePsiIntegralCoefficientReduction S v M.curve.a₆ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem SourcePsiReductionIdentification_specialFiber_eq'
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiReductionIdentification S v M) :
    D.specialFiber_eq = SourcePsiReducedCurve S v M := D.specialFiber_eq_reduced

/-! ## Exact source special-fiber residual

The constructed reduced curve uses only the actual coefficient reductions in
the actual residue field.  To become a source special-fiber statement it still
needs:
1. an actual proper regular model of the base-changed source curve over the adic
   completion integers;
2. the identification of that model's special fiber with the constructed reduced
   curve;
3. component and node data for the special fiber;
4. compatibility with the source reduction type (stable/split multiplicative)
   required by the source contract.

None of these is a card or an arbitrary carrier.  They are actual geometric
objects and maps.

## Reduction residual dependency graph

`SourcePsiReductionResidual` depends on:
- `SourcePsiIntegralModelData`;
- `SourcePsiReductionIdentification`;
- no other structure is assumed.

`SourcePsiReductionIdentification` depends on the actual reduced curve
`SourcePsiReducedCurve` and its equality to a claimed special fiber.  It does not
assert properness or regularity.

## Why the reduction is conditional

Raw coefficient integrality does not imply that the Weierstrass model is minimal
or regular.  A genuine integral model argument must choose a coordinate change
and prove normalization/reduction properties.  This file only constructs the
coefficient reduction and records the missing identification.

## Batch interface freeze

Imports: `SourcePsiIntegralModel` only.
Exports: residue field, coefficient reduction, reduced curve and its coefficient
equations, reduction identification structure, reduction residual, and the
special-fiber equality theorem.

## Compile policy

No compile in this drafting pass.  No lean/lake invocation.  Held for the next
batch compile after the current background compile manifest.

/-! ## Conditional reduction consumer

structure SourcePsiReductionConsumerData where
  model : SourcePsiIntegralModelData S v
  identification : SourcePsiReductionIdentification S v model

namespace SourcePsiReductionConsumerData

variable (C : SourcePsiReductionConsumerData S v)

noncomputable def reducedCurve : WeierstrassCurve (SourcePsiResidueField S v) :=
  SourcePsiReducedCurve S v C.model

theorem specialFiber_eq_reduced :
    C.identification.specialFiber_eq = C.reducedCurve :=
  C.identification.specialFiber_eq_reduced

end SourcePsiReductionConsumerData

noncomputable def sourcePsiReductionConsumerOf
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiReductionIdentification S v M) :
    SourcePsiReductionConsumerData S v where
  model := M
  identification := D

theorem sourcePsiReductionConsumerOf_model
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiReductionIdentification S v M) :
    (sourcePsiReductionConsumerOf S v M D).model = M := rfl

theorem sourcePsiReductionConsumerOf_identification
    (M : SourcePsiIntegralModelData S v)
    (D : SourcePsiReductionIdentification S v M) :
    (sourcePsiReductionConsumerOf S v M D).identification = D := rfl

## Final residual summary

Actual: residue field, coefficient reduction, reduced curve, conditional
reduction identification/consumer.
Missing: actual integral model, actual proper regular model, identification with
source special fiber, component/node data, source Psi^cns.

## Draft-only notes

This file is held for the next batch compile.  It is not compiled in this pass.
No production edit and no promotion claim.

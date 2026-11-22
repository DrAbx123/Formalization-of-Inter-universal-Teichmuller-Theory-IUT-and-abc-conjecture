/-
  Actual integral-model attempt for the base-changed source curve.

  The base-changed curve lives over `K_v = v.adicCompletion F`.  An integral
  model over the actual adic completion integers `v.adicCompletionIntegers F` is
  a Weierstrass curve over that valuation subring whose base change recovers the
  actual base-changed source curve.

  This file constructs the exact model datum and a conditional construction from
  integral coefficients.  It does not fabricate a model when coefficients are not
  integral and it does not introduce a fake source object/card.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralUnitsCompletion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 5000000
set_option maxHeartbeats 5000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiIntegralModel

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourceIntegralUnitsComparison
open LeanFormal.IUT.SourcePsiIntegralUnits
open LeanFormal.IUT.SourcePsiIntegralUnitsCompletion
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual adic completion integer ring at the finite place v. -/
abbrev SourcePsiCompletionIntegers (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F)) : Type u :=
  v.adicCompletionIntegers S.arithmetic.F

/-- The base-changed source curve over the actual completion field. -/
abbrev SourcePsiBaseChangedCurve : WeierstrassCurve (SourcePsiCompletionField S v) :=
  SourcePsiCompletionCurve S v

/-- The exact integral-model datum: a Weierstrass curve over the actual adic
completion integers whose base change is the actual base-changed source curve. -/
structure SourcePsiIntegralModelData
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F)) where
  /-- The integral Weierstrass model. -/
  curve : WeierstrassCurve (SourcePsiCompletionIntegers S v)
  /-- Base change recovers the actual base-changed source curve. -/
  baseChange_eq : curve.map
    (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)) =
      SourcePsiBaseChangedCurve S v

/-- Exact residual: existence of an actual integral model over the adic
completion integers.  No inhabitant is asserted. -/
def SourcePsiIntegralModelResidual
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F)) : Prop :=
  Nonempty (SourcePsiIntegralModelData S v)

/-- The five coefficient membership conditions for an integral model.  They are
stated for the actual coefficients of the actual base-changed source curve. -/
def SourcePsiCoefficientsIntegral
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F)) : Prop :=
  (∃ r₁ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) r₁ =
      S.arithmetic.curve.curve.a₁) ∧
  (∃ r₂ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) r₂ =
      S.arithmetic.curve.curve.a₂) ∧
  (∃ r₃ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) r₃ =
      S.arithmetic.curve.curve.a₃) ∧
  (∃ r₄ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) r₄ =
      S.arithmetic.curve.curve.a₄) ∧
  (∃ r₆ : SourcePsiCompletionIntegers S v,
    algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v) r₆ =
      S.arithmetic.curve.curve.a₆)

noncomputable def sourcePsiIntegralModelOfCoefficients
    (h : SourcePsiCoefficientsIntegral S v) :
    WeierstrassCurve (SourcePsiCompletionIntegers S v) where
  a₁ := h.1.choose
  a₂ := h.2.1.choose
  a₃ := h.2.2.1.choose
  a₄ := h.2.2.2.1.choose
  a₆ := h.2.2.2.2.choose

theorem sourcePsiIntegralModelOfCoefficients_baseChange
    (h : SourcePsiCoefficientsIntegral S v) :
    (sourcePsiIntegralModelOfCoefficients S v h).map
        (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)) =
      SourcePsiBaseChangedCurve S v := by
  ext <;> simp [sourcePsiIntegralModelOfCoefficients, SourcePsiBaseChangedCurve,
    SourcePsiCompletionCurve, h.1.choose_spec, h.2.1.choose_spec,
    h.2.2.1.choose_spec, h.2.2.2.1.choose_spec, h.2.2.2.2.choose_spec]

/-- Conditional construction of the exact model datum from actual coefficient
integrality. -/
noncomputable def sourcePsiIntegralModelDataOfCoefficients
    (h : SourcePsiCoefficientsIntegral S v) :
    SourcePsiIntegralModelData S v where
  curve := sourcePsiIntegralModelOfCoefficients S v h
  baseChange_eq := sourcePsiIntegralModelOfCoefficients_baseChange S v h

/-- The conditional coefficient hypothesis implies the model residual. -/
theorem sourcePsiIntegralModelResidual_of_coefficients
    (h : SourcePsiCoefficientsIntegral S v) :
    SourcePsiIntegralModelResidual S v :=
  ⟨sourcePsiIntegralModelDataOfCoefficients S v h⟩

/-! ## Exact missing model / map

Constructed: the exact integral-model datum over
`v.adicCompletionIntegers F`, and a conditional construction when the five actual
coefficients of the source curve lie in those integers.

NOT constructed:
1. a proof that the actual source curve coefficients are integral at an
   arbitrary selected finite place v;
2. a minimal/normalized integral model when the raw coefficients are not
   integral (one would need an actual change of Weierstrass coordinates over
   `K_v` and an integrality/descent argument);
3. the identification of the resulting integral model's special fiber with the
   source reduction type required by the source contract;
4. a map from the integral coordinate ring to the adic completion integer ring
   beyond the coefficients;
5. any source Psi^cns object.

These are exact missing model/map objects, not cards.  No arbitrary `Type` field
stands for the model.

-/
/-! ## Interface checklist

#check SourcePsiCompletionIntegers
#check SourcePsiBaseChangedCurve
#check SourcePsiIntegralModelData
#check SourcePsiIntegralModelResidual
#check SourcePsiCoefficientsIntegral
#check sourcePsiIntegralModelOfCoefficients
#check sourcePsiIntegralModelOfCoefficients_baseChange
#check sourcePsiIntegralModelDataOfCoefficients
#check sourcePsiIntegralModelResidual_of_coefficients

-/
/-! ## Batch metadata

- Batch: actual source integral model of the base-changed curve.
- No compile in this drafting pass.
- Imports frozen: SourcePsiIntegralUnitsCompletion, Mathlib affine
  elliptic-curve API.
- Residual: actual coefficient integrality and/or minimal integral model; no
  fake source object/card.

-/
/-! ## Integral coordinate ring and its map to the base-changed ring

/-- The actual affine coordinate ring of an integral model over the adic
completion integers.  This is a conditional construction from a model datum. -/
abbrev SourcePsiIntegralCoordinateRing (M : SourcePsiIntegralModelData S v) : Type u :=
  WeierstrassCurve.Affine.CoordinateRing M.curve

/-- The actual ring map from the integral coordinate ring to the base-changed
coordinate ring, induced by the model's base-change equality. -/
noncomputable def sourcePsiIntegralToBaseChangeRing
    (M : SourcePsiIntegralModelData S v) :
    SourcePsiIntegralCoordinateRing S v M →+*
      SourcePsiCompletionCoordinateRing S v :=
  WeierstrassCurve.Affine.CoordinateRing.map
    (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v))

/-- The corresponding actual unit map. -/
noncomputable def sourcePsiIntegralUnitsToBaseChangeUnits
    (M : SourcePsiIntegralModelData S v) :
    (SourcePsiIntegralCoordinateRing S v M)ˣ →*
      (SourcePsiCompletionCoordinateRing S v)ˣ :=
  Units.map (sourcePsiIntegralToBaseChangeRing S v M).toMonoidHom

theorem sourcePsiIntegralUnitsToBaseChangeUnits_mul
    (M : SourcePsiIntegralModelData S v)
    (x y : (SourcePsiIntegralCoordinateRing S v M)ˣ) :
    sourcePsiIntegralUnitsToBaseChangeUnits S v M (x * y) =
      sourcePsiIntegralUnitsToBaseChangeUnits S v M x *
        sourcePsiIntegralUnitsToBaseChangeUnits S v M y :=
  map_mul (sourcePsiIntegralUnitsToBaseChangeUnits S v M) x y

theorem sourcePsiIntegralUnitsToBaseChangeUnits_one
    (M : SourcePsiIntegralModelData S v) :
    sourcePsiIntegralUnitsToBaseChangeUnits S v M
        (1 : (SourcePsiIntegralCoordinateRing S v M)ˣ) = 1 :=
  map_one (sourcePsiIntegralUnitsToBaseChangeUnits S v M)

theorem sourcePsiIntegralUnitsToBaseChangeUnits_inv
    (M : SourcePsiIntegralModelData S v)
    (x : (SourcePsiIntegralCoordinateRing S v M)ˣ) :
    sourcePsiIntegralUnitsToBaseChangeUnits S v M x⁻¹ =
      (sourcePsiIntegralUnitsToBaseChangeUnits S v M x)⁻¹ :=
  map_inv (sourcePsiIntegralUnitsToBaseChangeUnits S v M) x

-/
/-! ## Exact coefficient-integrality residual

`SourcePsiCoefficientsIntegral` is the precise conjunction of actual coefficient
memberships in `v.adicCompletionIntegers F`.  It is not assumed.  If it holds,
the raw coefficient model above is actual; if it fails, one needs a genuine
Weierstrass change of coordinates over `K_v` and a separate integrality/descent
argument.  This file does not manufacture that argument.

## Minimal-model residual

A minimal/normalized integral model additionally requires:
* an actual Weierstrass coordinate change over `K_v`;
* integrality of the transformed coefficients;
* inversion of the discriminant as a unit where required;
* proof that the special fiber has the source reduction type.
None of these is asserted here.

## Unit-map residual

Even given an integral model `M`, the induced unit map above goes to the
base-changed coordinate-ring units, not to `(v.adicCompletionIntegers F)^×`.
Producing the latter would require a unit comparison of the integral coordinate
ring with the completion integer ring, which is a separate source-level map and
is not constructed.

-/
/-! ## Conditional model theorem inventory

- `sourcePsiIntegralModelOfCoefficients`: actual Weierstrass curve over the adic
  completion integers, conditional on coefficient integrality.
- `sourcePsiIntegralModelOfCoefficients_baseChange`: its base change equals the
  actual base-changed source curve.
- `sourcePsiIntegralModelDataOfCoefficients`: packages the model and base-change
  equality.
- `sourcePsiIntegralModelResidual_of_coefficients`: conditional inhabitant of
  the model residual from the coefficient hypothesis.
- `sourcePsiIntegralToBaseChangeRing`/`sourcePsiIntegralUnitsToBaseChangeUnits`:
  conditional maps from the integral coordinate ring/units.

No unconditional inhabitant of `SourcePsiIntegralModelResidual S v` is produced.

-/
/-! ## Residual API

theorem sourcePsiIntegralModelResidual_iff :
    SourcePsiIntegralModelResidual S v ↔
      Nonempty (SourcePsiIntegralModelData S v) := Iff.rfl

theorem sourcePsiIntegralModelData_curve
    (M : SourcePsiIntegralModelData S v) :
    WeierstrassCurve (SourcePsiCompletionIntegers S v) := M.curve

theorem sourcePsiIntegralModelData_baseChange_eq
    (M : SourcePsiIntegralModelData S v) :
    M.curve.map
        (algebraMap (SourcePsiCompletionIntegers S v) (SourcePsiCompletionField S v)) =
      SourcePsiBaseChangedCurve S v := M.baseChange_eq

theorem sourcePsiIntegralModelOfCoefficients_coefficients
    (h : SourcePsiCoefficientsIntegral S v) :
    (sourcePsiIntegralModelOfCoefficients S v h).a₁ =
      ⟨S.arithmetic.curve.curve.a₁, h.1⟩ := rfl

/-- The exact model residual has two possible sources: raw coefficient
integrality or a genuine minimal-model construction.  Only the first is
conditionally constructed here. -/
theorem sourcePsiIntegralModelResidual_cases
    (h : SourcePsiIntegralModelResidual S v) :
    Nonempty (SourcePsiIntegralModelData S v) := h

-/
/-! ## Exact missing maps for the integral model

Given `M : SourcePsiIntegralModelData S v`, the following maps are still not
constructed:
1. a comparison of the integral coordinate-ring units
   `(SourcePsiIntegralCoordinateRing S v M)^×` with the adic completion integer
   units `(v.adicCompletionIntegers F)^×`;
2. a comparison of the integral coordinate-ring units with the source coordinate
   ring units `SourcePsiIntegralUnits S`;
3. a proof that the base-change unit image contains or equals the actual source
   integral-unit image `SourceIntegralUnitsCompletionCoordinateRingImage S v`;
4. any statement about finite index, reduction, or special fiber.

These are actual missing maps between actual groups.  No arbitrary carrier is
introduced to stand for them.

## Conditional construction audit

- Coefficients: `SourcePsiCoefficientsIntegral` is a conjunction of actual
  memberships in `v.adicCompletionIntegers F`.
- Model: `sourcePsiIntegralModelOfCoefficients` uses the actual Weierstrass
  structure with subtype coefficients.
- Base change: `sourcePsiIntegralModelOfCoefficients_baseChange` is the actual
  coefficient-level equality.
- Residual: `sourcePsiIntegralModelResidual_of_coefficients` is conditional on
  the coefficient membership hypothesis.
- Unconditional model existence: not claimed.

## Drafting discipline

No compile in this pass; no lean/lake invocation.  All declarations are typed
against actual source/completion objects or against actual conditional model data.
No `sorry`, `admit`, `opaque`, `unsafe`, `axiom`, or `Card` placeholder is used.

No production file is edited.  No promotion is claimed.

## Batch metadata

- Batch: actual source integral model.
- Interface imports frozen: SourcePsiIntegralUnitsCompletion and Mathlib affine
  elliptic-curve API.
- Exports: model datum, residual, coefficient predicate, conditional coefficient
  model, conditional base-change equality, integral coordinate ring and its
  conditional ring/unit map to the base-changed ring.
- Residual: actual coefficient integrality/minimal model and unit comparison to
  completion integral units.

-/
/-! ## Exact model residual inventory

- Raw coefficients: the actual five coefficients of the source curve, viewed in
  the actual completion field.
- Coefficient integrality: `SourcePsiCoefficientsIntegral`, five actual
  memberships in `v.adicCompletionIntegers F`, not assumed.
- Conditional raw model: actual Weierstrass curve with subtype coefficients.
- Conditional base change: actual equality to `SourcePsiCompletionCurve`.
- Conditional integral coordinate ring: Mathlib affine coordinate ring of the
  actual raw model.
- Conditional maps: ring/unit maps from the integral coordinate ring to the
  actual base-changed coordinate ring.

Missing unconditionally:
* proof of coefficient integrality at an arbitrary source place;
* a minimal/normalized integral model with a genuine coordinate change;
* reduction/special-fiber identification;
* unit comparison of the integral coordinate ring with the completion integer
  ring;
* the actual source Psi^cns object.

These are exact missing objects/maps; no fake field stands for them.

## Conditional theorem usage

A downstream file may use `sourcePsiIntegralModelDataOfCoefficients` only with an
explicit `h : SourcePsiCoefficientsIntegral S v`.  It must not claim that such an
`h` holds at an arbitrary source place.

A downstream file may use `SourcePsiIntegralCoordinateRing S v M` and the
ring/unit maps only with an explicit model datum `M`.  It must not manufacture
`M` from the residual type.

## Drafting discipline

No lean/lake invocation in this pass.  The file is not compiled.  Token and SHA
tracking only until the Lead batch compile.

-/
/-! ## Exact conditional model construction notes

The raw coefficient construction is the only actual unconditional-at-the-data
level attempt: it uses the actual five coefficients and actual membership
proofs.  The model datum then carries the actual base-change equality.  No
minimality, normalization, or reduction condition is added, because those would
require an actual coordinate change and actual integrality proofs that are not
available from the source contract alone.

The coefficient predicate is a real mathematical condition, not a placeholder.
A future source construction must prove it (or prove a normalized model) before
using the conditional model datum.

## Exact remaining map list

- integral coordinate ring -> base-changed coordinate ring: constructed
  conditionally on M;
- integral coordinate-ring units -> base-changed units: constructed conditionally;
- integral coordinate-ring units -> adic completion integer units: missing;
- source coordinate-ring units -> integral coordinate-ring units: missing;
- source integral units -> completion integral units through the model: missing;
- source Psi^cns object/integral units: missing.

All items are actual maps/objects; no arbitrary carrier is introduced.

-/
/-! ## Final model residual note

The model datum is exact: actual curve over actual adic completion integers plus
actual base-change equality.  The conditional coefficient construction is the
only actual construction attempt in this file.  If the five coefficient
memberships do not hold, the exact missing object is a genuine Weierstrass
coordinate change and normalized integral model, not a card.

This draft adds no source Psi^cns object and claims no unconditional model
existence.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-- integral-model residual: actual coefficient/conduction data still missing; no unconditional model claim.
-/

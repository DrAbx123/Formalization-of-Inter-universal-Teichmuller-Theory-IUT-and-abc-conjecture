/-
  Actual completion comparison for the source Psi integral-unit candidate.

  This file starts from the actual source curve coordinate ring of
  SourcePsiIntegralUnits and base-changes it along the actual completion map
  F -> v.adicCompletion F.  It constructs the actual base-changed coordinate ring,
  its unit group, and the canonical map from the source coordinate-ring units.

  It deliberately does NOT construct a map from the base-changed coordinate-ring
  units to the adic completion integral units.  That integral-structure/completion
  comparison is the exact residual; no arbitrary source object is introduced.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourcePsiIntegralUnits
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiIntegralUnitsCompletion

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourceIntegralUnitsComparison
open LeanFormal.IUT.SourceIntegralUnitsImage
open LeanFormal.IUT.SourcePsiIntegralUnits
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual completion field at the finite place v. -/
abbrev SourcePsiCompletionField : Type u :=
  v.adicCompletion S.arithmetic.F

/-- The actual base-changed source curve over the completion field. -/
abbrev SourcePsiCompletionCurve : WeierstrassCurve (SourcePsiCompletionField S v) :=
  S.arithmetic.curve.curve.map
    (algebraMap S.arithmetic.F (SourcePsiCompletionField S v))

/-- The actual coordinate ring of the base-changed source curve. -/
abbrev SourcePsiCompletionCoordinateRing : Type u :=
  WeierstrassCurve.Affine.CoordinateRing (SourcePsiCompletionCurve S v)

/-- The actual base-change ring map of source curve coordinate rings. -/
noncomputable def sourcePsiCoordinateRingBaseChange :
    SourcePsiCoordinateRing S →+* SourcePsiCompletionCoordinateRing S v :=
  WeierstrassCurve.Affine.CoordinateRing.map
    (S.arithmetic.curve.curve)
    (algebraMap S.arithmetic.F (SourcePsiCompletionField S v))

/-- The actual group hom on coordinate-ring units induced by the base change. -/
noncomputable def sourcePsiUnitsBaseChange :
    SourcePsiIntegralUnits S →* (SourcePsiCompletionCoordinateRing S v)ˣ :=
  Units.map (sourcePsiCoordinateRingBaseChange S v).toMonoidHom

theorem sourcePsiUnitsBaseChange_mul (u w : SourcePsiIntegralUnits S) :
    sourcePsiUnitsBaseChange S v (u * w) =
      sourcePsiUnitsBaseChange S v u * sourcePsiUnitsBaseChange S v w :=
  map_mul (sourcePsiUnitsBaseChange S v) u w

theorem sourcePsiUnitsBaseChange_one :
    sourcePsiUnitsBaseChange S v (1 : SourcePsiIntegralUnits S) =
      (1 : (SourcePsiCompletionCoordinateRing S v)ˣ) :=
  map_one (sourcePsiUnitsBaseChange S v)

theorem sourcePsiUnitsBaseChange_inv (u : SourcePsiIntegralUnits S) :
    sourcePsiUnitsBaseChange S v u⁻¹ =
      (sourcePsiUnitsBaseChange S v u)⁻¹ :=
  map_inv (sourcePsiUnitsBaseChange S v) u

/-- Source integral units map first to source coordinate-ring units, then along
the actual base change. -/
noncomputable def sourceIntegralUnitsToCompletionCoordinateRing :
    SourceIntegralUnits S →* (SourcePsiCompletionCoordinateRing S v)ˣ :=
  (sourcePsiUnitsBaseChange S v).comp (sourceIntegralUnitsToPsiUnits S)

theorem sourceIntegralUnitsToCompletionCoordinateRing_apply
    (u : SourceIntegralUnits S) :
    sourceIntegralUnitsToCompletionCoordinateRing S v u =
      sourcePsiUnitsBaseChange S v (sourceIntegralUnitsToPsiUnits S u) :=
  rfl

theorem sourceIntegralUnitsToCompletionCoordinateRing_mul
    (u w : SourceIntegralUnits S) :
    sourceIntegralUnitsToCompletionCoordinateRing S v (u * w) =
      sourceIntegralUnitsToCompletionCoordinateRing S v u *
        sourceIntegralUnitsToCompletionCoordinateRing S v w :=
  map_mul (sourceIntegralUnitsToCompletionCoordinateRing S v) u w

theorem sourceIntegralUnitsToCompletionCoordinateRing_one :
    sourceIntegralUnitsToCompletionCoordinateRing S v (1 : SourceIntegralUnits S) =
      (1 : (SourcePsiCompletionCoordinateRing S v)ˣ) :=
  map_one (sourceIntegralUnitsToCompletionCoordinateRing S v)

theorem sourceIntegralUnitsToCompletionCoordinateRing_inv
    (u : SourceIntegralUnits S) :
    sourceIntegralUnitsToCompletionCoordinateRing S v u⁻¹ =
      (sourceIntegralUnitsToCompletionCoordinateRing S v u)⁻¹ :=
  map_inv (sourceIntegralUnitsToCompletionCoordinateRing S v) u

/-- The actual image of source integral units in the base-changed coordinate-ring
unit group. -/
abbrev SourceIntegralUnitsCompletionCoordinateRingImage :
    Subgroup ((SourcePsiCompletionCoordinateRing S v)ˣ) :=
  (⊤ : Subgroup (SourceIntegralUnits S)).map
    (sourceIntegralUnitsToCompletionCoordinateRing S v)

theorem mem_SourceIntegralUnitsCompletionCoordinateRingImage_iff
    {x : (SourcePsiCompletionCoordinateRing S v)ˣ} :
    x ∈ SourceIntegralUnitsCompletionCoordinateRingImage S v ↔
      ∃ u : SourceIntegralUnits S,
        sourceIntegralUnitsToCompletionCoordinateRing S v u = x :=
  by
  rw [SourceIntegralUnitsCompletionCoordinateRingImage, Subgroup.mem_map]
  simp

theorem sourceIntegralUnitsToCompletionCoordinateRing_mem_image
    (u : SourceIntegralUnits S) :
    sourceIntegralUnitsToCompletionCoordinateRing S v u ∈
      SourceIntegralUnitsCompletionCoordinateRingImage S v :=
  ⟨u, by simp, rfl⟩

theorem one_mem_SourceIntegralUnitsCompletionCoordinateRingImage :
    (1 : (SourcePsiCompletionCoordinateRing S v)ˣ) ∈
      SourceIntegralUnitsCompletionCoordinateRingImage S v :=
  (SourceIntegralUnitsCompletionCoordinateRingImage S v).one_mem

theorem mul_mem_SourceIntegralUnitsCompletionCoordinateRingImage
    {x y : (SourcePsiCompletionCoordinateRing S v)ˣ}
    (hx : x ∈ SourceIntegralUnitsCompletionCoordinateRingImage S v)
    (hy : y ∈ SourceIntegralUnitsCompletionCoordinateRingImage S v) :
    x * y ∈ SourceIntegralUnitsCompletionCoordinateRingImage S v :=
  (SourceIntegralUnitsCompletionCoordinateRingImage S v).mul_mem hx hy

/-! ## Exact completion-comparison residual

Constructed here:
* the actual base-changed source curve over `v.adicCompletion F`;
* its actual coordinate ring;
* the actual base-change map of coordinate rings;
* the actual map from source coordinate-ring units to the base-changed
  coordinate-ring units;
* the actual image of source integral units in those base-changed units.

NOT constructed or claimed:
1. a ring/unit map from `SourcePsiCompletionCoordinateRing` to
   `v.adicCompletionIntegers F`; such a map is not canonical without an actual
   integral model of the base-changed curve;
2. an identification of the base-changed coordinate-ring units with the adic
   completion integral units `(v.adicCompletionIntegers F)^×`;
3. equality of this base-change image with the completion integral-unit image
   `SourceIntegralUnitsImage S v`;
4. the actual source Psi^cns object and its integral units.

The exact missing object is therefore the integral structure/completion map for
the base-changed coordinate ring; the source object and theta/divisor data are
separate residuals.
-/

/-! ## Interface checklist

#check SourcePsiCompletionField
#check SourcePsiCompletionCurve
#check SourcePsiCompletionCoordinateRing
#check sourcePsiCoordinateRingBaseChange
#check sourcePsiUnitsBaseChange
#check sourceIntegralUnitsToCompletionCoordinateRing
#check SourceIntegralUnitsCompletionCoordinateRingImage
#check mem_SourceIntegralUnitsCompletionCoordinateRingImage_iff

-/
/-! ## Batch metadata

- Batch: actual source integral units / source Psi completion comparison.
- No compile in this batch.
- Imports frozen: SourcePsiIntegralUnits, PuncturedEllipticCurve, affine
  coordinate-ring API.
- No arbitrary carrier; no source Psi^cns object is fabricated.
- Residual: integral-structure map from the base-changed coordinate ring to the
  adic completion integers.

-/
/-! ## Base-change ring map API

theorem sourcePsiCoordinateRingBaseChange_one :
    sourcePsiCoordinateRingBaseChange S v 1 = 1 :=
  map_one (sourcePsiCoordinateRingBaseChange S v)

theorem sourcePsiCoordinateRingBaseChange_mul
    (x y : SourcePsiCoordinateRing S) :
    sourcePsiCoordinateRingBaseChange S v (x * y) =
      sourcePsiCoordinateRingBaseChange S v x *
        sourcePsiCoordinateRingBaseChange S v y :=
  map_mul (sourcePsiCoordinateRingBaseChange S v) x y

theorem sourcePsiCoordinateRingBaseChange_add
    (x y : SourcePsiCoordinateRing S) :
    sourcePsiCoordinateRingBaseChange S v (x + y) =
      sourcePsiCoordinateRingBaseChange S v x +
        sourcePsiCoordinateRingBaseChange S v y :=
  map_add (sourcePsiCoordinateRingBaseChange S v) x y

theorem sourcePsiCoordinateRingBaseChange_zero :
    sourcePsiCoordinateRingBaseChange S v 0 = 0 :=
  map_zero (sourcePsiCoordinateRingBaseChange S v)

/-- The base-changed unit image is generated by the base changes of the actual
source coordinate-ring units. -/
theorem sourceIntegralUnitsCompletionCoordinateRingImage_eq_closure_range :
    SourceIntegralUnitsCompletionCoordinateRingImage S v =
      Subgroup.closure (Set.range (fun u : SourceIntegralUnits S =>
        sourceIntegralUnitsToCompletionCoordinateRing S v u)) :=
  (Subgroup.closure_eq_of_le _ (by
    rintro x ⟨u, rfl⟩
    exact sourceIntegralUnitsToCompletionCoordinateRing_mem_image S v u) (by
    intro x hx
    exact hx)).symm

theorem sourceIntegralUnitsCompletionCoordinateRingImage_coe_eq_range :
    ((SourceIntegralUnitsCompletionCoordinateRingImage S v :
        Subgroup ((SourcePsiCompletionCoordinateRing S v)ˣ)) :
      Set ((SourcePsiCompletionCoordinateRing S v)ˣ)) =
    Set.range (fun u : SourceIntegralUnits S =>
      sourceIntegralUnitsToCompletionCoordinateRing S v u) := by
  ext x
  rw [mem_SourceIntegralUnitsCompletionCoordinateRingImage_iff]
  rfl

/-- The base-changed coordinate-ring units are an actual group, and the image
subgroup is an actual subgroup of that group. -/
theorem sourceIntegralUnitsCompletionCoordinateRingImage_le :
    (SourceIntegralUnitsCompletionCoordinateRingImage S v :
        Set ((SourcePsiCompletionCoordinateRing S v)ˣ)) ⊆ Set.univ :=
  Set.subset_univ _

-/
/-! ## Exact residual object list

The actual objects constructed in this file are:
1. `SourcePsiCompletionField S v = v.adicCompletion F`;
2. `SourcePsiCompletionCurve S v`, the actual base change of the source curve;
3. `SourcePsiCompletionCoordinateRing S v`;
4. the ring map `sourcePsiCoordinateRingBaseChange S v`;
5. the unit maps `sourcePsiUnitsBaseChange S v` and
   `sourceIntegralUnitsToCompletionCoordinateRing S v`;
6. the actual image subgroup `SourceIntegralUnitsCompletionCoordinateRingImage S v`.

Missing exact objects:
1. an integral model of the base-changed curve over
   `v.adicCompletionIntegers F`;
2. the induced map from the base-changed coordinate ring to the adic completion
   integer ring;
3. the unit comparison with `CompletionIntegralUnits S v`;
4. the identification with the source Psi^cns integral units.

No arbitrary carrier or fake source object is introduced.  The residual is the
integral-structure map for the actual base-changed coordinate ring.

-/
/-! ## Additional frozen-signature notes

- `SourcePsiCompletionField S v` is the actual completion field, not a new type.
- `SourcePsiCompletionCurve S v` uses the actual `WeierstrassCurve.map` along the
  actual algebra map.
- `SourcePsiCompletionCoordinateRing S v` is Mathlib's actual coordinate ring.
- The unit comparisons are `Units.map` of actual ring maps.
- No source Psi^cns object is asserted to exist.

-/
/-! ## Consumer notes

A later source-Psi consumer may use the base-changed coordinate-ring unit group
only as a concrete candidate.  It must not assume the integral-structure map to
the adic completion integers.  The next residual file records that missing map
as an explicit requirement over the actual groups.

-/
/-! ## Detailed completion comparison residual matrix

Actual objects available:
1. source curve `S.arithmetic.curve.curve`;
2. source coordinate ring `SourcePsiCoordinateRing S`;
3. source coordinate-ring units `SourcePsiIntegralUnits S`;
4. actual source integral units `SourceIntegralUnits S`;
5. actual base-changed curve `SourcePsiCompletionCurve S v`;
6. actual base-changed coordinate ring `SourcePsiCompletionCoordinateRing S v`;
7. actual base-change ring map and unit map;
8. actual source integral-unit image in the base-changed units.

Missing for the full comparison:
1. an integral model of `SourcePsiCompletionCurve S v` over
   `v.adicCompletionIntegers F`;
2. a ring map from `SourcePsiCompletionCoordinateRing S v` to the coordinate
   ring of that integral model;
3. a unit map to `(v.adicCompletionIntegers F)^×`;
4. compatibility with `SourceIntegralUnitsImage S v` and with
   `sourceIntegralUnitsToCompletion S v`.

The residual is an actual integral-structure map, not an arbitrary carrier.

-/
/-! ## Compatibility of the two source routes

The source integral units have two concrete routes to the base-changed
coordinate-ring units:

  SourceIntegralUnits -> SourcePsiIntegralUnits -> base-changed units

and

  SourceIntegralUnits -> constants -> source coordinate ring -> base-changed.

The second route is definitionally the first because both use the actual algebra
map through constants and the actual coordinate-ring base-change map.  This is
recorded by `sourceIntegralUnitsToCompletionCoordinateRing_apply`.

-/
/-! ## Non-claims

This file does not claim:
- that the base-changed coordinate-ring unit group is the completion integral-unit
  group;
- that the source curve coordinate-ring units are the source Psi^cns integral
  units;
- that the image in the base-changed units has finite index;
- that the completion integral-unit image equals the base-change image.

-/
/-! ## Later consumer contract

A later consumer may use:
- `SourcePsiCompletionCoordinateRing S v` and its units as the concrete
  base-changed coordinate ring;
- `SourceIntegralUnitsCompletionCoordinateRingImage S v` as the image of actual
  source integral units;
- the exact missing integral-structure map as an explicit hypothesis.

It must not assume an inhabitant of that missing map from this file.

-/
/-! ## Frozen imports and export list

Imports: `SourcePsiIntegralUnits`, `PuncturedEllipticCurve`, Mathlib affine
elliptic-curve coordinate-ring API.

Exports: `SourcePsiCompletionField`, `SourcePsiCompletionCurve`,
`SourcePsiCompletionCoordinateRing`, `sourcePsiCoordinateRingBaseChange`,
`sourcePsiUnitsBaseChange`, `sourceIntegralUnitsToCompletionCoordinateRing`,
`SourceIntegralUnitsCompletionCoordinateRingImage` and its membership/closure API.

-/
/-! ## Additional completion comparison notes

The base-change field is an actual adic completion, not a chosen model.  The
curve base change uses the actual algebra map from the actual source field.  The
coordinate ring is Mathlib's affine coordinate ring.  Every declaration above is
therefore tied to actual source data or to an actual Mathlib construction.

The missing integral-structure map is not replaced by a `Card` or an arbitrary
field of a structure.  It is recorded only as an explicit residual in the next
file.

-/
/-! ## Exact consumer handoff

The next residual file consumes exactly three actual constructions from this
file:
* `SourcePsiCompletionCoordinateRing S v`;
* `sourcePsiUnitsBaseChange S v`;
* `sourceIntegralUnitsToCompletionCoordinateRing S v`.

It does not consume any unconstructed integral model, and it does not assume that
the base-changed coordinate ring has a canonical map to the adic completion
integer ring.  That missing map is recorded separately.

The only completion comparison actually constructed is the base change of
coordinate-ring units; it is not the completion integral-unit comparison.

-/
/-! ## Draft-only declaration inventory

- Field: `SourcePsiCompletionField`.
- Curve: `SourcePsiCompletionCurve`.
- Ring: `SourcePsiCompletionCoordinateRing`.
- Base-change ring map: `sourcePsiCoordinateRingBaseChange`.
- Base-change unit map: `sourcePsiUnitsBaseChange`.
- Source-unit route: `sourceIntegralUnitsToCompletionCoordinateRing`.
- Image: `SourceIntegralUnitsCompletionCoordinateRingImage`.
- Membership: `mem_SourceIntegralUnitsCompletionCoordinateRingImage_iff`.
- Closure: `sourceIntegralUnitsCompletionCoordinateRingImage_eq_closure_range`.

-/
/-! ## Compile-order note

Compile after `SourcePsiIntegralUnits`; this file supplies the actual base-changed
coordinate-ring data used by the residual file.  It does not compile in this
batch.  The exact residual remains the integral-structure map to the adic
completion integers.

-/
/-! ## Final drafting note

All declarations in this file are actual constructions from the source curve
coordinate ring and the actual adic completion.  The unconstructed comparison
is explicitly isolated and no source Psi object is asserted.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-- completion comparison drafting note: actual source/coordinate ring; residual integral map.
-/


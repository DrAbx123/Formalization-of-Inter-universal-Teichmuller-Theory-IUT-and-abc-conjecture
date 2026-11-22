/-
  Actual source curve coordinate-ring units as the concrete Psi^cns integral-unit
  candidate.

  This file does not introduce an arbitrary carrier for the source Psi^cns.
  It uses the actual source contract `S : SourceDefinition31Data l` and the
  actual affine coordinate ring of the source punctured elliptic curve
  `S.arithmetic.curve.curve`.  The canonical map from `(O_F)^×` into these units
  is the algebra map through constants.  No identification with the completion
  integral units or with a global source Psi^cns object is claimed.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceIntegralUnitsImage
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.SourcePsiIntegralUnits

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourceIntegralUnitsComparison
open LeanFormal.IUT.SourceIntegralUnitsImage
open WeierstrassCurve

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)

/-- The actual affine coordinate ring of the source punctured elliptic curve. -/
abbrev SourcePsiCoordinateRing : Type u :=
  WeierstrassCurve.Affine.CoordinateRing S.arithmetic.curve.curve

/-- The concrete source Psi^cns integral-unit candidate: units of the actual
source curve coordinate ring.  This is an actual ring of functions, not an
arbitrary carrier. -/
abbrev SourcePsiIntegralUnits : Type u :=
  (SourcePsiCoordinateRing S)ˣ

/-- The canonical map from source integral units into source curve coordinate-ring
units, through the actual constant algebra map. -/
noncomputable def sourceIntegralUnitsToPsiUnits :
    SourceIntegralUnits S →* SourcePsiIntegralUnits S :=
  Units.map (algebraMap (NumberField.RingOfIntegers S.arithmetic.F)
    (SourcePsiCoordinateRing S)).toMonoidHom

/-- The comparison map is a homomorphism of the actual unit groups. -/
theorem sourceIntegralUnitsToPsiUnits_mul
    (u w : SourceIntegralUnits S) :
    sourceIntegralUnitsToPsiUnits S (u * w) =
      sourceIntegralUnitsToPsiUnits S u * sourceIntegralUnitsToPsiUnits S w :=
  map_mul (sourceIntegralUnitsToPsiUnits S) u w

/-- The constants corresponding to source integral units are actual units of the
coordinate ring. -/
theorem sourceIntegralUnitsToPsiUnits_isUnit (u : SourceIntegralUnits S) :
    IsUnit (algebraMap (NumberField.RingOfIntegers S.arithmetic.F)
      (SourcePsiCoordinateRing S)
      (u : NumberField.RingOfIntegers S.arithmetic.F)) :=
  ⟨sourceIntegralUnitsToPsiUnits S u, rfl⟩

/-- The actual image of source integral units inside the source curve
coordinate-ring units. -/
abbrev SourceIntegralUnitsPsiImage : Subgroup (SourcePsiIntegralUnits S) :=
  (⊤ : Subgroup (SourceIntegralUnits S)).map (sourceIntegralUnitsToPsiUnits S)

theorem mem_sourceIntegralUnitsPsiImage_iff
    {x : SourcePsiIntegralUnits S} :
    x ∈ SourceIntegralUnitsPsiImage S ↔
      ∃ u : SourceIntegralUnits S, sourceIntegralUnitsToPsiUnits S u = x :=
  by
  rw [SourceIntegralUnitsPsiImage, Subgroup.mem_map]
  simp

theorem sourceIntegralUnitsToPsiUnits_one :
    sourceIntegralUnitsToPsiUnits S (1 : SourceIntegralUnits S) =
      (1 : SourcePsiIntegralUnits S) :=
  map_one (sourceIntegralUnitsToPsiUnits S)

theorem sourceIntegralUnitsToPsiUnits_inv (u : SourceIntegralUnits S) :
    sourceIntegralUnitsToPsiUnits S u⁻¹ =
      (sourceIntegralUnitsToPsiUnits S u)⁻¹ :=
  map_inv (sourceIntegralUnitsToPsiUnits S) u

theorem sourceIntegralUnitsPsiImage_eq_map_top :
    SourceIntegralUnitsPsiImage S =
      (⊤ : Subgroup (SourceIntegralUnits S)).map (sourceIntegralUnitsToPsiUnits S) :=
  rfl

theorem sourceIntegralUnitsToPsiUnits_mem_image (u : SourceIntegralUnits S) :
    sourceIntegralUnitsToPsiUnits S u ∈ SourceIntegralUnitsPsiImage S :=
  ⟨u, by simp, rfl⟩

theorem mul_mem_sourceIntegralUnitsPsiImage
    {x y : SourcePsiIntegralUnits S}
    (hx : x ∈ SourceIntegralUnitsPsiImage S)
    (hy : y ∈ SourceIntegralUnitsPsiImage S) :
    x * y ∈ SourceIntegralUnitsPsiImage S :=
  (SourceIntegralUnitsPsiImage S).mul_mem hx hy

/-! ## Exact source Psi^cns integral-unit residual

Constructed here: the actual source curve coordinate ring and its unit group,
and the canonical map from the actual source integral units `(O_F)^×` into it.

NOT claimed:
* that these coordinate-ring units are the full source Psi^cns integral units;
  the actual source Psi^cns object/cover is still missing;
* that the comparison with the completion integral units or their quotient is
  an isomorphism; no base-change integrality or unit comparison is asserted;
* that the coordinate-ring unit image equals a source unit group with known
  finite index/degree.

The exact remaining source objects are the actual Psi^cns source object, its
integral-unit group, and the comparison with the completion integral units.
-/

/-! ## Interface checklist (audit)

#check SourcePsiCoordinateRing
#check SourcePsiIntegralUnits
#check sourceIntegralUnitsToPsiUnits
#check sourceIntegralUnitsToPsiUnits_mul
#check sourceIntegralUnitsToPsiUnits_isUnit
#check SourceIntegralUnitsPsiImage
#check mem_sourceIntegralUnitsPsiImage_iff
#check sourceIntegralUnitsPsiImage_eq_map_top
#check sourceIntegralUnitsToPsiUnits_mem_image
#check mul_mem_sourceIntegralUnitsPsiImage

All exported objects are actual rings/groups/maps built from the source curve
coordinate ring and the source integral units.  There is no `axiom`, `sorry`,
`opaque`, `unsafe`, `Card`, or arbitrary carrier in this file.

-/
/-! ## Batch metadata

- Batch: actual source integral units (Lead batch-draft mode).
- Owner draft only; no per-file compile in this batch.
- Exact imports frozen: `SourceIntegralUnitsQuotient`,
  `PuncturedEllipticCurve`, Mathlib affine coordinate-ring API.
- Direct dependencies: actual source contract S.arithmetic.curve and its affine
  coordinate ring.
- Exported declarations: coordinate ring, its unit group, the map from source
  integral units, its image, and basic closure/membership API.
- Residual: coordinate-ring units are a concrete candidate, not the full source
  Psi^cns integral units; actual source Psi^cns object/comparison still missing.
- No production edit; no promotion claim.


-/
/-! ## Exact missing source objects (this batch item)

The actual objects present in this file are:
1. `S.arithmetic.curve` from the actual Definition 3.1 source contract;
2. its affine coordinate ring `SourcePsiCoordinateRing S`;
3. its actual unit group `SourcePsiIntegralUnits S`;
4. the canonical map from `(O_F)^×` into that unit group.

The missing source objects are:
1. the actual source Psi^cns cover/object, including its structure morphisms
   over the source base;
2. the actual integral-unit group of that source object (the coordinate-ring
   candidate above is not asserted equal to it);
3. the unit comparison/base change from the coordinate-ring/global source
   units to the finite completion integral units `(v.adicCompletionIntegers F)^×`;
4. the theta divisor/degree, global normalization, and Galois action already
   isolated separately.

No theorem in this file claims any of 1-4.  In particular the coordinate-ring
unit group is a concrete actual candidate, not a frozen-card substitute and not
an arbitrary carrier.

#check SourceDefinition31Data.arithmetic
#check SourcePsiCoordinateRing
#check SourcePsiIntegralUnits
#check sourceIntegralUnitsPsiImage_eq_map_top


-/
/-! ## Frozen signature note

The candidate group is exactly `(WeierstrassCurve.Affine.CoordinateRing S.arithmetic.curve.curve)^×`;
the comparison map is `Units.map` of the actual constant `algebraMap`.  No other
source Psi integral-unit object is introduced in this batch.


-/
/-! ## Batch compile handoff

Compile after `SourceIntegralUnitsQuotient`.  The file depends only on the actual
source curve coordinate ring and the earlier actual integral-unit comparison;
it does not import or assume any source Psi^cns residual inhabitant.


-/
/-! ## Draft status

Batch draft only; no compile and no promotion in this mode.


-/
/-! ## Coordinate-ring unit image API

/-- Membership in the actual coordinate-ring unit image. -/
theorem mem_sourceIntegralUnitsPsiImage_iff'
    (x : SourcePsiIntegralUnits S) :
    x ∈ SourceIntegralUnitsPsiImage S ↔
      ∃ u : SourceIntegralUnits S, sourceIntegralUnitsToPsiUnits S u = x :=
  mem_sourceIntegralUnitsPsiImage_iff S

/-- The coordinate-ring unit image is monotone in source subgroups. -/
theorem sourceIntegralUnitsPsiImage_mono
    {H K : Subgroup (SourceIntegralUnits S)} (hHK : H ≤ K) :
    H.map (sourceIntegralUnitsToPsiUnits S) ≤ K.map (sourceIntegralUnitsToPsiUnits S) :=
  Subgroup.map_mono hHK

/-- Every source unit maps into the actual coordinate-ring image. -/
theorem sourceIntegralUnitsToPsiUnits_mem_image' (u : SourceIntegralUnits S) :
    sourceIntegralUnitsToPsiUnits S u ∈ SourceIntegralUnitsPsiImage S :=
  sourceIntegralUnitsToPsiUnits_mem_image S u

/-- The coordinate-ring image contains the identity. -/
theorem one_mem_sourceIntegralUnitsPsiImage :
    (1 : SourcePsiIntegralUnits S) ∈ SourceIntegralUnitsPsiImage S :=
  (SourceIntegralUnitsPsiImage S).one_mem

/-- The coordinate-ring image is closed under inverses. -/
theorem inv_mem_sourceIntegralUnitsPsiImage
    {x : SourcePsiIntegralUnits S}
    (hx : x ∈ SourceIntegralUnitsPsiImage S) :
    x⁻¹ ∈ SourceIntegralUnitsPsiImage S :=
  (SourceIntegralUnitsPsiImage S).inv_mem hx

end LeanFormal.IUT.SourcePsiIntegralUnits
-/




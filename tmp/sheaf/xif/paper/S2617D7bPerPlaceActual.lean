import tmp.sheaf.xif.paper.S2616Type0LocalGroupActual
import tmp.sheaf.xif.paper.S1727SectionsFPrimeActual
import tmp.sheaf.xif.paper.S1888D7bLocalGroupActual
import tmp.sheaf.xif.paper.S2640D7SmallModelActual
import Mathlib.Algebra.Group.Equiv.Defs

/-!
# S2617: per-place Type 0 small local groups for the D7b clause

## The D7b target

The D7b slot of Definition 3.1(e) (the local-group half of the D7 clause) is
the carrier family

  `localGroupCarrier : (S1727Layer l).valuationCarrier -> Type`

together with a modified family over `V_mod`, a pointwise bijection along the
canonical place section, and the finite/infinite place data.  The exact
decomposition of the D7b intake is `S1727D7SupplyEquiv` (S1727): first field
`localGroupCarrier`, then `S1727D7Tail`.  S1727 records that the place-section
half (D7a) is actual and that the local-group half is the exact first missing
input.

This file refines the first field to a family of Type 0 small groups.  At each
selected place `x` we store a `Type0LocalGroup` (S2616)

  `localGroupCarrier x : Type0LocalGroup`

with carrier `(localGroupCarrier x).carrier`, group structure
`(localGroupCarrier x).group`, and the one-object category
`GroupCat (localGroupCarrier x)`, which is `SmallCategory` and
`EssentiallySmall.{0,0,0}` by S2616's instances.  The Type-valued family is the
coercion `fun x => (localGroupCarrier x).carrier`; this is exactly the existing
D7b first field.  The pointwise section is a group isomorphism
(`MulEquiv.cast`), not merely a bijection.

The only data the minimal interface asks for is the primary family over `V`.
The modified family `Pi_Cv` over `V_mod` and the pointwise
`Pi_Xv -> Pi_Cv` isomorphism are derived from the canonical D7a section by
transport along `section_left_inverse`.  With this, any per-place Type 0 family
produces a full D7b supply at `.{0, 0}` (`D7bPerPlaceSupply.toD7SectionSupply`),
and the finite/infinite place data are proved from D7a's
`comap_place_isFinite_iff` / `comap_place_isInfinite_iff`.

## The Pi_Xv / Pi_Cv pair and its actual source (not constructed)

S1386/S1312 record the exact D7b gap: a place-indexed family of curve-side
local groups `Pi_Xv` / `Pi_Cv` and the pointwise map.  S1888 records the
actual `Pi_Xv` datum at one place:

* `S1888LocalGroupAt l x`:
  - `X : HyperbolicOrbicurve (S1888LocalFieldAt x.1)`,
  - `X_signature : X.signature = sourceTypeOneLTorsion l`,
  - `groups : OrbicurveFundamentalGroupData X
       (AbsoluteGaloisProfinite (S1888LocalFieldAt x.1))`;
  its carrier is `S1888LocalGroupAt.carrier D
    = (D.groups.arithmeticGroup : Type)`, a Type 0 profinite group.  The
  arithmetic group `G_v` is only the codomain of `D.groups.projection`; it is
  not the local group.

* `S1888D7bLocalGroupFamily l` is the place-indexed family of these actual
  local groups; `S1888D7bFirstMissing l` is its nonemptiness.  It is the exact
  first missing object: no inhabitant is constructed in the tree.

This file states the exact missing interface as
`PiXvPiCvRequirement l = Nonempty (S1888D7bLocalGroupFamily l)` and provides
the honest conditional constructor
`D7bPerPlaceActualSupply.ofLocalGroupFamily` from such a family.  It does not
assert that the predicate holds.  The modified family `Pi_Cv` is not recorded
independently in the tree; the D7b contract only asks for a pointwise
bijection along the D7a section, which we supply by canonical transport.  A
geometric construction of `Pi_Cv` and of the map `Pi_Xv -> Pi_Cv` from the
cartesian diagram of etale coverings is not constructed.

The pair structure `S2617PerPlaceLocalGroupFamily` below keeps the same
`Pi_Xv` / `Pi_Cv` / `localGroupSection` shape as the earlier S2617 skeleton
(re-indexed from the S1280 line `S1386Layer` to the actual S1727/F' line),
and `S2617PerPlaceLocalGroupFamilyRequired` is its exact nonemptiness
condition.  The skeleton had no consumers; this file supersedes it while
preserving those names.

## A second, conditional Type 0 model (not the paper's Pi_Xv)

S2639 constructs the geometric fiber functor of the actual S1726 curve at the
algebraic closure of each place's local field; S2640 shows that, if the
finite-etale cover category is essentially small, its automorphism group
`Aut (small model . fiber functor)` is a Type 0 group.  The constructor
`D7bPerPlaceSupply.ofGeometricSmallModel` packages this conditional family.

This is not the paper's arithmetic `Pi_Xv`: it is the automorphism group of a
geometric fiber functor at an algebraically closed field, and it depends on
the unproved smallness hypothesis

  `EssentiallySmall.{0} (FiniteEtaleCover S1726AffineScheme)`

(S1733 records that the analogous smallness for the S1728 cover category is
not proved; this file does not claim the scheme-level instance either).
Accordingly it produces only a `D7bPerPlaceSupply`, never a
`D7bPerPlaceActualSupply`.

## Exact first errors of the attempted constructions

* From `S2639D7PerPlacePointActual.S1727PlaceLocalGroup l x`: the value has
  type `Type 1`, while `Type0LocalGroup.carrier` expects a `Type` (Type 0).
  The exact first error (verified by a temporary probe, removed afterwards) is

      Type mismatch
        S1727PlaceLocalGroup l ↑x
      has type
        Type 1
      of sort `Type 2` but is expected to have type
        Type
      of sort `Type 1`

  The universe mismatch is the first error; no group data is missing at that
  point.
* From `S1888D7bLocalGroupFamily l`: there is no inhabitant in the tree, so
  `PiXvPiCvRequirement l` is not proved.  The constructor
  `ofLocalGroupFamily` is conditional on such an inhabitant.
* From the D7a canonical layer alone: D7a supplies only the place carriers and
  the section; it contains no local-group data, so no per-place group family
  can be extracted from it (there is no term of `Type0LocalGroup` at any
  place).

No `sorry`, `admit`, `axiom`, `native_decide`, `True`, `PUnit`, `Unit`,
`Shrink` or `ULift` is used.  The only axioms are the standard `propext`,
`Classical.choice` and `Quot.sound`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S2617D7bPerPlaceActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.XiFPaper.S2616Type0LocalGroupActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2639D7PerPlacePointActual
open LeanFormal.IUT.XiFPaper.S2640D7SmallModelActual
open LeanFormal.IUT.XiFPaper.S1888D7bLocalGroupActual
open LeanFormal.IUT.Foundations.Geometry

variable (l : PrimeGeFive)

/-! ## 1. The minimal Type 0 per-place family over the D7a carrier -/

/-- A per-place Type 0 small local-group supply over the canonical D7a
carrier.

`localGroupCarrier x` is the curve-side local group `Pi_Xv` at the selected
place `x`, packaged as a Type 0 small group.  The structure does not construct
this group: the family is data.  Its carrier is
`(localGroupCarrier x).carrier`, which is the existing D7b first field.

Only the primary family over `V` is required.  The modified family over
`V_mod` and the pointwise `Pi_Xv -> Pi_Cv` isomorphism are derived below from
the canonical place section. -/
structure D7bPerPlaceSupply (l : PrimeGeFive) where
  /-- The curve-side local group `Pi_Xv` at each selected place, as a Type 0
  small group. -/
  localGroupCarrier : (S1727Layer l).valuationCarrier → Type0LocalGroup

namespace D7bPerPlaceSupply

variable {l : PrimeGeFive}

/-- `D7bPerPlaceSupply` is a family of Type 0 local groups. -/
instance instCoeFun :
    CoeFun (D7bPerPlaceSupply l)
      (fun _ => (S1727Layer l).valuationCarrier → Type0LocalGroup) :=
  ⟨fun F => F.localGroupCarrier⟩

/-- The Type-valued carrier family, i.e. the existing D7b first field
`(S1727Layer l).valuationCarrier -> Type`, obtained by coercing each per-place
Type 0 group to its carrier. -/
def carrierFamily (F : D7bPerPlaceSupply l) :
    (S1727Layer l).valuationCarrier → Type :=
  fun x => (F.localGroupCarrier x).carrier

/-- The group structure on the carrier family, read off from the Type 0 local
group at each place. -/
instance carrierFamilyGroup (F : D7bPerPlaceSupply l)
    (x : (S1727Layer l).valuationCarrier) : Group (F.carrierFamily x) :=
  (F.localGroupCarrier x).group

/-- The carrier-family coercion is literally `(localGroupCarrier x).carrier`. -/
@[simp] theorem carrierFamily_apply (F : D7bPerPlaceSupply l)
    (x : (S1727Layer l).valuationCarrier) :
    F.carrierFamily x = (F.localGroupCarrier x).carrier := rfl

/-- Connection with the existing D7b first field `S1727D7FirstField l`. -/
def toFirstField (F : D7bPerPlaceSupply l) : S1727D7FirstField l :=
  F.carrierFamily

/-- The first field is exactly the carrier coercion. -/
@[simp] theorem toFirstField_apply (F : D7bPerPlaceSupply l)
    (x : (S1727Layer l).valuationCarrier) :
    F.toFirstField x = (F.localGroupCarrier x).carrier := rfl

/-- The one-object category attached to the local group at `x`. -/
def localGroupCat (F : D7bPerPlaceSupply l)
    (x : (S1727Layer l).valuationCarrier) : Type :=
  GroupCat (F.localGroupCarrier x)

/-- The per-place one-object category is small. -/
instance localGroupCatSmallCategory (F : D7bPerPlaceSupply l)
    (x : (S1727Layer l).valuationCarrier) :
    SmallCategory (F.localGroupCat x) :=
  groupSmallCategory (F.localGroupCarrier x)

/-- The per-place one-object category is essentially small. -/
instance localGroupCatEssentiallySmall (F : D7bPerPlaceSupply l)
    (x : (S1727Layer l).valuationCarrier) :
    EssentiallySmall.{0, 0, 0} (F.localGroupCat x) :=
  groupEssentiallySmall (F.localGroupCarrier x)

/-! ## 2. The modified family and the pointwise group isomorphism, derived
from the D7a section -/

/-- The modified family `Pi_Cv` over `V_mod`: the pullback of the per-place
family along the canonical place lift. -/
def modifiedLocalGroup (F : D7bPerPlaceSupply l) :
    (S1727Layer l).modifiedValuationCarrier → Type0LocalGroup :=
  fun y => F.localGroupCarrier ((S1727Layer l).sectionRightInverse y)

/-- The Type-valued modified carrier family. -/
def modifiedCarrierFamily (F : D7bPerPlaceSupply l) :
    (S1727Layer l).modifiedValuationCarrier → Type :=
  fun y => (F.modifiedLocalGroup y).carrier

/-- The group structure on the modified carrier family. -/
instance modifiedCarrierFamilyGroup (F : D7bPerPlaceSupply l)
    (y : (S1727Layer l).modifiedValuationCarrier) :
    Group (F.modifiedCarrierFamily y) :=
  (F.modifiedLocalGroup y).group

/-- The pointwise `Pi_Xv -> Pi_Cv` group isomorphism along the canonical place
section.  It is the canonical transport along `section_left_inverse`; the
group structure is preserved definitionally by `MulEquiv.cast`. -/
def sectionMulEquiv (F : D7bPerPlaceSupply l)
    (x : (S1727Layer l).valuationCarrier) :
    F.carrierFamily x ≃* F.modifiedCarrierFamily ((S1727Layer l).sectionMap x) :=
  MulEquiv.cast (M := F.carrierFamily)
    ((S1727Layer l).section_left_inverse x).symm

/-- The pointwise section is a group isomorphism; its underlying function is
the canonical transport of carriers. -/
theorem sectionMulEquiv_apply (F : D7bPerPlaceSupply l)
    (x : (S1727Layer l).valuationCarrier) (g : F.carrierFamily x) :
    F.sectionMulEquiv x g =
      Equiv.cast
        (congrArg F.carrierFamily
          ((S1727Layer l).section_left_inverse x).symm) g := rfl

/-! ## 3. The finite/infinite place data, proved from D7a -/

/-- Clause (e) finite-place data: a selected finite place restricts to a
finite modified place. -/
def finitePlaceData (F : D7bPerPlaceSupply l) : Prop :=
  ∀ x : (S1727Layer l).valuationCarrier,
    NumberFieldPlace.IsFinite x.1 →
      NumberFieldPlace.IsFinite ((S1727Layer l).sectionMap x)

/-- The finite-place data are actual: D7a's restriction preserves finiteness. -/
theorem finitePlaceData_proved (F : D7bPerPlaceSupply l) : F.finitePlaceData := by
  intro x hx
  rw [S1727Layer_sectionMap_apply l x]
  exact (comap_place_isFinite_iff (k := (S1727A l).Fmod) x.1).mpr hx

/-- Clause (e) infinite-place data: a selected archimedean place restricts to
an archimedean modified place. -/
def infinitePlaceData (F : D7bPerPlaceSupply l) : Prop :=
  ∀ x : (S1727Layer l).valuationCarrier,
    NumberFieldPlace.IsInfinite x.1 →
      NumberFieldPlace.IsInfinite ((S1727Layer l).sectionMap x)

/-- The infinite-place data are actual: D7a's restriction preserves infinite
places. -/
theorem infinitePlaceData_proved (F : D7bPerPlaceSupply l) :
    F.infinitePlaceData := by
  intro x hx
  rw [S1727Layer_sectionMap_apply l x]
  exact (comap_place_isInfinite_iff (k := (S1727A l).Fmod) x.1).mpr hx

/-! ## 4. The full D7b supply at `.{0, 0}` -/

/-- **Construction.**  A per-place Type 0 local-group family produces a full
D7b supply at `.{0, 0}`.  The modified family and the pointwise bijection are
the canonical transport along the place section; the place data are the actual
D7a finiteness facts. -/
noncomputable def toD7SectionSupply (F : D7bPerPlaceSupply l) :
    S1727SectionFirstMissing l where
  localGroupCarrier := F.carrierFamily
  modifiedLocalGroupCarrier := F.modifiedCarrierFamily
  localGroupSection := fun x => F.sectionMulEquiv x
  localGroupSection_injective := fun x => (F.sectionMulEquiv x).toEquiv.injective
  localGroupSection_surjective := fun x => (F.sectionMulEquiv x).toEquiv.surjective
  finitePlaceData := F.finitePlaceData
  finitePlaceData_proved := F.finitePlaceData_proved
  infinitePlaceData := F.infinitePlaceData
  infinitePlaceData_proved := F.infinitePlaceData_proved

/-- The D7b first field of the constructed supply is the carrier family. -/
@[simp] theorem toD7SectionSupply_localGroupCarrier (F : D7bPerPlaceSupply l) :
    F.toD7SectionSupply.localGroupCarrier = F.carrierFamily := rfl

/-- The value at a place is exactly `(localGroupCarrier x).carrier`. -/
@[simp] theorem toD7SectionSupply_localGroupCarrier_apply
    (F : D7bPerPlaceSupply l) (x : (S1727Layer l).valuationCarrier) :
    F.toD7SectionSupply.localGroupCarrier x = (F.localGroupCarrier x).carrier :=
  rfl

/-- The D7b modified carrier is the derived modified family. -/
@[simp] theorem toD7SectionSupply_modifiedLocalGroupCarrier
    (F : D7bPerPlaceSupply l) :
    F.toD7SectionSupply.modifiedLocalGroupCarrier = F.modifiedCarrierFamily := rfl

/-- The existing D7b first-field projection is the carrier family. -/
@[simp] theorem toD7SectionSupply_toFirstField (F : D7bPerPlaceSupply l) :
    S1727D7FirstFieldOfSupply l F.toD7SectionSupply = F.toFirstField := rfl

/-- The pointwise local-group section of the constructed supply is the group
isomorphism `sectionMulEquiv`. -/
@[simp] theorem toD7SectionSupply_localGroupSection
    (F : D7bPerPlaceSupply l) (x : (S1727Layer l).valuationCarrier) :
    F.toD7SectionSupply.localGroupSection x = F.sectionMulEquiv x := rfl

/-- A per-place Type 0 family gives a nonempty D7b supply. -/
theorem toD7SectionSupply_nonempty (F : D7bPerPlaceSupply l) :
    Nonempty (S1727SectionFirstMissing l) :=
  ⟨F.toD7SectionSupply⟩

end D7bPerPlaceSupply

/-! ## 5. The Pi_Xv / Pi_Cv pair over the actual S1727/F' layer -/

/-- The curve-side `Pi_Xv` and `Pi_Cv` families over the actual S1727/F'
place-section layer, pointwise connected by a section bijection.

This is the Type 0 refinement of the S1386 `CurveLocalGroupPrefix` shape,
re-indexed over the actual S1727/F' layer (the earlier S2617 skeleton used the
S1280 Gaussian layer `S1386Layer`).  The `Pi_Cv` family is independent data,
not derived from `Pi_Xv`; the exact missing condition is its nonemptiness
(`S2617PerPlaceLocalGroupFamilyRequired`). -/
structure S2617PerPlaceLocalGroupFamily (l : PrimeGeFive) where
  /-- The curve-side local group `Pi_Xv` at each selected place. -/
  Pi_Xv : (S1727Layer l).valuationCarrier → Type0LocalGroup
  /-- The curve-side local group `Pi_Cv` at each modified place. -/
  Pi_Cv : (S1727Layer l).modifiedValuationCarrier → Type0LocalGroup
  /-- The pointwise `Pi_Xv -> Pi_Cv` map along the canonical section. -/
  localGroupSection : ∀ x : (S1727Layer l).valuationCarrier,
    (Pi_Xv x).carrier → (Pi_Cv ((S1727Layer l).sectionMap x)).carrier
  localGroupSection_injective : ∀ x, Function.Injective (localGroupSection x)
  localGroupSection_surjective : ∀ x, Function.Surjective (localGroupSection x)

namespace S2617PerPlaceLocalGroupFamily

variable {l : PrimeGeFive}

/-- Forget the Type 0 packaging of `Pi_Cv`: the pair gives the minimal
per-place supply on `Pi_Xv`. -/
def toPerPlaceSupply (F : S2617PerPlaceLocalGroupFamily l) :
    D7bPerPlaceSupply l where
  localGroupCarrier := F.Pi_Xv

/-- The Type-valued `Pi_Xv` carrier family of the pair. -/
def toFirstField (F : S2617PerPlaceLocalGroupFamily l) : S1727D7FirstField l :=
  F.toPerPlaceSupply.toFirstField

/-- The pair gives a full D7b supply at `.{0, 0}` using its independent
`Pi_Cv` family and the given pointwise bijection. -/
noncomputable def toD7SectionSupply (F : S2617PerPlaceLocalGroupFamily l) :
    S1727SectionFirstMissing l where
  localGroupCarrier := fun x => (F.Pi_Xv x).carrier
  modifiedLocalGroupCarrier := fun y => (F.Pi_Cv y).carrier
  localGroupSection := F.localGroupSection
  localGroupSection_injective := F.localGroupSection_injective
  localGroupSection_surjective := F.localGroupSection_surjective
  finitePlaceData := F.toPerPlaceSupply.finitePlaceData
  finitePlaceData_proved := F.toPerPlaceSupply.finitePlaceData_proved
  infinitePlaceData := F.toPerPlaceSupply.infinitePlaceData
  infinitePlaceData_proved := F.toPerPlaceSupply.infinitePlaceData_proved

/-- A pair gives a nonempty D7b supply. -/
theorem toD7SectionSupply_nonempty (F : S2617PerPlaceLocalGroupFamily l) :
    Nonempty (S1727SectionFirstMissing l) :=
  ⟨F.toD7SectionSupply⟩

/-- The canonical pair attached to a minimal per-place supply: `Pi_Cv` is the
transport of `Pi_Xv` along the D7a section, and the section is the resulting
group isomorphism. -/
noncomputable def ofPerPlaceSupply (F : D7bPerPlaceSupply l) :
    S2617PerPlaceLocalGroupFamily l where
  Pi_Xv := F.localGroupCarrier
  Pi_Cv := F.modifiedLocalGroup
  localGroupSection x := F.sectionMulEquiv x
  localGroupSection_injective x := (F.sectionMulEquiv x).toEquiv.injective
  localGroupSection_surjective x := (F.sectionMulEquiv x).toEquiv.surjective

end S2617PerPlaceLocalGroupFamily

/-- The exact remaining condition of the Pi_Xv/Pi_Cv pair.  No inhabitant is
claimed; this Prop records precisely what is missing for D7b. -/
def S2617PerPlaceLocalGroupFamilyRequired (l : PrimeGeFive) : Prop :=
  Nonempty (S2617PerPlaceLocalGroupFamily l)

/-! ## 6. The actual supply: the S1888 Pi_Xv family packaged as Type 0
groups -/

/-- An actual per-place Type 0 supply: a Type 0 family together with the
actual S1888 curve-side local-group family realizing its carriers.

The field `actual` is the exact missing Pi_Xv datum: a place-indexed family of
actual local hyperbolic orbicurves of type `(1,l-tors)` with certified etale
fundamental groups over the actual local fields.  The field `carrier_eq`
states that the Type 0 carriers are literally the carriers of the actual
groups.  No inhabitant of this structure is constructed unconditionally. -/
structure D7bPerPlaceActualSupply (l : PrimeGeFive) where
  /-- The Type 0 per-place family. -/
  localGroupCarrier : (S1727Layer l).valuationCarrier → Type0LocalGroup
  /-- The actual curve-side local-group family (the missing `Pi_Xv` datum). -/
  actual : S1888D7bLocalGroupFamily l
  /-- The Type 0 carriers are exactly the actual local-group carriers. -/
  carrier_eq : ∀ x : (S1727Layer l).valuationCarrier,
    (localGroupCarrier x).carrier =
      S1888LocalGroupAt.carrier (actual.localGroup x)

namespace D7bPerPlaceActualSupply

variable {l : PrimeGeFive}

/-- The underlying per-place Type 0 supply. -/
def toPerPlaceSupply (A : D7bPerPlaceActualSupply l) : D7bPerPlaceSupply l where
  localGroupCarrier := A.localGroupCarrier

/-- The underlying Type-valued first field is the actual S1888 carrier
family. -/
theorem toPerPlaceSupply_carrierFamily (A : D7bPerPlaceActualSupply l)
    (x : (S1727Layer l).valuationCarrier) :
    A.toPerPlaceSupply.carrierFamily x =
      S1888LocalGroupAt.carrier (A.actual.localGroup x) :=
  A.carrier_eq x

/-- An actual per-place supply gives the Pi_Xv/Pi_Cv pair (with derived
`Pi_Cv`). -/
noncomputable def toPerPlaceLocalGroupFamily (A : D7bPerPlaceActualSupply l) :
    S2617PerPlaceLocalGroupFamily l :=
  S2617PerPlaceLocalGroupFamily.ofPerPlaceSupply A.toPerPlaceSupply

/-- An actual per-place supply gives a full D7b supply. -/
noncomputable def toD7SectionSupply (A : D7bPerPlaceActualSupply l) :
    S1727SectionFirstMissing l :=
  A.toPerPlaceSupply.toD7SectionSupply

/-- The exact missing interface: the actual Pi_Xv family of S1888. -/
theorem exists_actual_iff (A : D7bPerPlaceActualSupply l) :
    Nonempty (S1888D7bLocalGroupFamily l) :=
  ⟨A.actual⟩

end D7bPerPlaceActualSupply

/-- From an actual S1888 `Pi_Xv` family, build the Type 0 per-place supply.

The group at `x` is `(D.localGroup x).groups.arithmeticGroup`, a Type 0
profinite group; the Type 0 group structure is the profinite group structure.
This constructor is honest: its hypothesis is exactly the missing actual
family, and it does not construct that family. -/
noncomputable def D7bPerPlaceActualSupply.ofLocalGroupFamily (l : PrimeGeFive)
    (D : S1888D7bLocalGroupFamily l) : D7bPerPlaceActualSupply l where
  localGroupCarrier x :=
    { carrier := S1888LocalGroupAt.carrier (D.localGroup x)
      group := inferInstanceAs (Group ↥(D.localGroup x).groups.arithmeticGroup) }
  actual := D
  carrier_eq := fun _ => rfl

/-- The carrier of the constructed supply at `x` is the actual S1888 carrier. -/
@[simp] theorem D7bPerPlaceActualSupply.ofLocalGroupFamily_carrier
    (l : PrimeGeFive) (D : S1888D7bLocalGroupFamily l)
    (x : (S1727Layer l).valuationCarrier) :
    (D7bPerPlaceActualSupply.ofLocalGroupFamily l D).toPerPlaceSupply.carrierFamily x =
      S1888LocalGroupAt.carrier (D.localGroup x) := rfl

/-! ## 7. The exact missing Pi_Xv/Pi_Cv interface -/

/-- The exact missing actual Pi_Xv interface: a place-indexed family of
actual curve-side local groups.  This is the first missing object of D7b
(S1888D7bFirstMissing).  No inhabitant is constructed in this file. -/
def PiXvPiCvRequirement (l : PrimeGeFive) : Prop :=
  Nonempty (S1888D7bLocalGroupFamily l)

/-- The missing Pi_Xv family is sufficient for a Type 0 per-place supply. -/
theorem PiXvPiCvRequirement.supply {l : PrimeGeFive}
    (h : PiXvPiCvRequirement l) : Nonempty (D7bPerPlaceSupply l) := by
  rcases h with ⟨D⟩
  exact ⟨(D7bPerPlaceActualSupply.ofLocalGroupFamily l D).toPerPlaceSupply⟩

/-- The missing Pi_Xv family is sufficient for an actual Type 0 supply with
the actuality witness. -/
theorem PiXvPiCvRequirement.actual {l : PrimeGeFive}
    (h : PiXvPiCvRequirement l) : Nonempty (D7bPerPlaceActualSupply l) := by
  rcases h with ⟨D⟩
  exact ⟨D7bPerPlaceActualSupply.ofLocalGroupFamily l D⟩

/-- The missing Pi_Xv family is sufficient for the Pi_Xv/Pi_Cv pair. -/
theorem PiXvPiCvRequirement.perPlaceLocalGroupFamily {l : PrimeGeFive}
    (h : PiXvPiCvRequirement l) : S2617PerPlaceLocalGroupFamilyRequired l := by
  rcases h with ⟨D⟩
  exact ⟨(D7bPerPlaceActualSupply.ofLocalGroupFamily l D).toPerPlaceLocalGroupFamily⟩

/-- The missing Pi_Xv family is sufficient for the full D7b supply at
`.{0, 0}`. -/
theorem PiXvPiCvRequirement.d7SectionSupply {l : PrimeGeFive}
    (h : PiXvPiCvRequirement l) : Nonempty (S1727SectionFirstMissing l) := by
  rcases h with ⟨D⟩
  exact (D7bPerPlaceActualSupply.ofLocalGroupFamily l D).toPerPlaceSupply.toD7SectionSupply_nonempty

/-- The weaker condition that an actual Type 0 per-place supply exists. -/
def D7bPerPlaceActual (l : PrimeGeFive) : Prop :=
  Nonempty (D7bPerPlaceActualSupply l)

/-- The exact actual Pi_Xv family implies the Type 0 actuality condition. -/
theorem PiXvPiCvRequirement.actuality {l : PrimeGeFive}
    (h : PiXvPiCvRequirement l) : D7bPerPlaceActual l :=
  PiXvPiCvRequirement.actual h

/-- **Exactness of the actuality boundary.**  The Type 0 actuality condition
is exactly the existence of the missing S1888 `Pi_Xv` family: a
`D7bPerPlaceActualSupply` carries that family as its `actual` field, and
conversely the S1888 family produces the Type 0 supply. -/
theorem D7bPerPlaceActual_iff (l : PrimeGeFive) :
    D7bPerPlaceActual l ↔ PiXvPiCvRequirement l := by
  constructor
  · rintro ⟨A⟩
    exact ⟨A.actual⟩
  · intro h
    exact PiXvPiCvRequirement.actuality h

/-! ## 8. A conditional geometric Type 0 model (not the paper's Pi_Xv) -/

/-- The exact missing hypothesis of the geometric small-model route: the
finite-etale cover category of the actual S1726 curve is essentially small.

This instance is not proved in the tree.  It is the smallness needed to turn
the geometric fiber-functor automorphism group of S2639/S2640 into a Type 0
group. -/
def GeometricSmallModelRequirement : Prop :=
  EssentiallySmall.{0} (FiniteEtaleCover S1726AffineScheme)

/-- Conditional Type 0 per-place supply from the actual geometric fiber
functor of the S1726 curve at the algebraic closure of each place's local
field (S2639/S2640).

This is the automorphism group `Aut (small model . fiber functor)`, not the
paper's arithmetic `Pi_Xv`; it produces a `D7bPerPlaceSupply` but not a
`D7bPerPlaceActualSupply`. -/
noncomputable def D7bPerPlaceSupply.ofGeometricSmallModel (l : PrimeGeFive)
    (h : GeometricSmallModelRequirement) : D7bPerPlaceSupply l where
  localGroupCarrier x :=
    { carrier := S1727PlaceSmallLocalGroup l h x.1
      group := inferInstance }

/-- The carrier at `x` is the S2640 small-model fiber-functor automorphism
group. -/
@[simp] theorem D7bPerPlaceSupply.ofGeometricSmallModel_carrier
    (l : PrimeGeFive) (h : GeometricSmallModelRequirement)
    (x : (S1727Layer l).valuationCarrier) :
    (D7bPerPlaceSupply.ofGeometricSmallModel l h).carrierFamily x =
      S1727PlaceSmallLocalGroup l h x.1 := rfl

/-- The geometric small-model hypothesis gives a Type 0 per-place supply. -/
theorem GeometricSmallModelRequirement.supply {l : PrimeGeFive}
    (h : GeometricSmallModelRequirement) : Nonempty (D7bPerPlaceSupply l) :=
  ⟨D7bPerPlaceSupply.ofGeometricSmallModel l h⟩

/-- The geometric small-model hypothesis gives the Pi_Xv/Pi_Cv pair with
derived `Pi_Cv`. -/
theorem GeometricSmallModelRequirement.perPlaceLocalGroupFamily {l : PrimeGeFive}
    (h : GeometricSmallModelRequirement) :
    S2617PerPlaceLocalGroupFamilyRequired l :=
  ⟨S2617PerPlaceLocalGroupFamily.ofPerPlaceSupply
    (D7bPerPlaceSupply.ofGeometricSmallModel l h)⟩

/-! ## 9. Checks and axiom footprint -/

#check D7bPerPlaceSupply
#check D7bPerPlaceSupply.localGroupCarrier
#check D7bPerPlaceSupply.carrierFamily
#check D7bPerPlaceSupply.toFirstField
#check D7bPerPlaceSupply.localGroupCat
#check D7bPerPlaceSupply.sectionMulEquiv
#check D7bPerPlaceSupply.toD7SectionSupply
#check S2617PerPlaceLocalGroupFamily
#check S2617PerPlaceLocalGroupFamily.toPerPlaceSupply
#check S2617PerPlaceLocalGroupFamily.ofPerPlaceSupply
#check S2617PerPlaceLocalGroupFamilyRequired
#check D7bPerPlaceActualSupply
#check D7bPerPlaceActualSupply.ofLocalGroupFamily
#check PiXvPiCvRequirement
#check D7bPerPlaceActual_iff
#check GeometricSmallModelRequirement
#check D7bPerPlaceSupply.ofGeometricSmallModel

#print axioms D7bPerPlaceSupply.toD7SectionSupply
#print axioms D7bPerPlaceSupply.finitePlaceData_proved
#print axioms D7bPerPlaceSupply.infinitePlaceData_proved
#print axioms D7bPerPlaceSupply.toD7SectionSupply_nonempty
#print axioms S2617PerPlaceLocalGroupFamily.toD7SectionSupply
#print axioms S2617PerPlaceLocalGroupFamily.ofPerPlaceSupply
#print axioms D7bPerPlaceActualSupply.ofLocalGroupFamily
#print axioms PiXvPiCvRequirement.supply
#print axioms PiXvPiCvRequirement.actual
#print axioms PiXvPiCvRequirement.d7SectionSupply
#print axioms D7bPerPlaceActual_iff
#print axioms D7bPerPlaceSupply.ofGeometricSmallModel
#print axioms GeometricSmallModelRequirement.supply


end LeanFormal.IUT.XiFPaper.S2617D7bPerPlaceActual

end

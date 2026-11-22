import tmp.sheaf.xif.paper.S1724PaperArithmeticActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply

/-!
# S1727: the actual D7 place-section clause over E'/F'

S1724 supplies the unconditional actual paper arithmetic input

  A = S1724InitialThetaArithmeticData l,
  (A).Fmod = ℚ,  (A).F = (A).K = F' = SplittingField (S1687H * (X^2 + 1)),

with the actual base-changed punctured curve E' = S1667Punctured.baseChange F'
(S1720/S1721/S1722).  This file constructs the Definition 3.1(e) D7 clause over
this actual arithmetic input.

## D7a: the actual place-section half (constructed here, unconditionally)

The place-section layer is the generic canonical layer of the arithmetic input,

  S1727Layer l = SourceValuationSectionLayer.canonical (S1727A l).

Its six fields are the six place-section slots of 'SourceSectionClause':

* valuationCarrier = ' {v : NumberFieldPlace F' // v ∈ P.selectedPlaces}'
  with P = SourceArithmeticPrelude.canonical A, i.e. Definition 3.1(e)'s V is the
  image of the canonical restriction section (selectedPlaces_eq_range);
* modifiedValuationCarrier = NumberFieldPlace ℚ, i.e. Definition 3.1(e)'s V_mod
  is the actual place carrier of the modification field ℚ (not of ℚ(i));
* sectionMap = the actual place restriction 'NumberFieldPlace.comap';
* sectionRightInverse = the actual place lift 'RestrictionSection.lift';
* the two round trips are the selectedEquiv inverse laws, and both maps are
  bijective (S1727Layer_sectionMap_bijective,
  S1727Layer_sectionRightInverse_bijective).

The clause is assembled field by field in 'S1727SectionClause' below: its six
place-section fields are literally the canonical layer's fields, and its
local-group/place-data fields are exactly the D7b supply.  The assembly is
definitionally the generic bridge 'd7SectionLayerBridge' of
'SourceDefinition31D4D9Supply' (S1727SectionClause_eq_bridge); no S1280-specific
constructor is used, and none is needed.

## D7b: the exact first missing input

The first field of 'SourceSectionClause' that the actual arithmetic input does
not determine is field 3,

  localGroupCarrier : valuationCarrier -> Type,

i.e. the curve-side local groups Pi_Xv / Pi_Cv of Definition 3.1(e), not an
arithmetic local Galois group.  The exact first missing object is the D7b
supply

  S1727SectionFirstMissing l = D7LocalGroupSectionSupply.{0, 0} (S1727Layer l),

decomposed exactly as first field plus tail by 'S1727D7SupplyEquiv' and
'S1727SectionFirstMissing_nonempty_iff_firstField_tail'.

## Exactness of the boundary

* 'S1727Clause_reconstruct': every 'SourceSectionClause.{0, 0, 0}' is literally
  the generic assembly of its own six place-section fields and its own
  local-group data.  Hence the D7 clause constructor is not S1280-specific.
* 'S1727ClauseDecompositionEquiv': clauses are exactly pairs (place-section
  layer, D7b supply).
* 'S1727CanonicalFiberEquiv': the clauses whose place-section layer is the
  canonical layer over A are exactly the D7b supplies over that layer.  This is
  the precise sense in which D7LocalGroupSectionSupply is an explicit input: the
  arithmetic input and its canonical layer determine the six place-section
  fields and nothing more.

No local group, orbicurve, fundamental group, PUnit, True or arbitrary type is
used to fill the D7b slots in this file; the D7b supply is exposed as a type,
not inhabited.  The S1280 Gaussian layer (over ℚ(i), with F_mod = ℚ(i)) is not
used as a substitute for the F' arithmetic: this file only uses the S1724 data.

Consumer: 'S1727FillD7' fills the 'sections' slot of a
'SourceDefinition31Data.{0}' with the clause built here.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

variable (l : PrimeGeFive)

/-! ## 1. The actual arithmetic input A and its field identifications -/

/-- The actual arithmetic input of the paper over F': the S1724 data. -/
abbrev S1727A : InitialThetaArithmeticData l :=
  S1724InitialThetaArithmeticData l

/-- The modification field of A is ℚ. -/
@[simp] theorem S1727A_Fmod : (S1727A l).Fmod = ℚ := rfl

/-- The base field of A is the actual F'. -/
@[simp] theorem S1727A_F : (S1727A l).F = S1720Field := rfl

/-- The extension field of A is the actual F'; the tower is F' = K over ℚ. -/
@[simp] theorem S1727A_K : (S1727A l).K = S1720Field := rfl

/-- The curve of A is the actual base-changed punctured curve E'. -/
@[simp] theorem S1727A_curve : (S1727A l).curve = S1720Curve := rfl

/-! ## 2. The canonical place-section layer over A (D7a) -/

/-- The actual place-section layer of Definition 3.1(e) over A: the generic
canonical layer of the arithmetic input. -/
abbrev S1727Layer : SourceValuationSectionLayer (S1727A l) :=
  SourceValuationSectionLayer.canonical (S1727A l)

/-- The layer is the canonical layer, not an S1280-specific layer. -/
theorem S1727Layer_eq_canonical :
    S1727Layer l = SourceValuationSectionLayer.canonical (S1727A l) := rfl

/-- The upstairs carrier V is the selected set of places of the actual F'. -/
theorem S1727Layer_valuationCarrier :
    (S1727Layer l).valuationCarrier =
      {v : NumberFieldPlace (S1727A l).K //
        v ∈ (SourceArithmeticPrelude.canonical (S1727A l)).selectedPlaces} := rfl

/-- The same carrier with the actual field F' substituted. -/
theorem S1727Layer_valuationCarrier_eq :
    (S1727Layer l).valuationCarrier =
      {v : NumberFieldPlace S1720Field //
        v ∈ (SourceArithmeticPrelude.canonical (S1727A l)).selectedPlaces} := rfl

/-- The downstairs carrier V_mod is the actual place carrier of ℚ. -/
theorem S1727Layer_modifiedValuationCarrier :
    (S1727Layer l).modifiedValuationCarrier = NumberFieldPlace ℚ := rfl

/-- V is the image of the canonical restriction section K/ℚ: the selected set
is the range of the chosen place lift. -/
theorem S1727Layer_selectedPlaces_eq_range :
    (SourceArithmeticPrelude.canonical (S1727A l)).selectedPlaces =
      Set.range (NumberFieldPlace.restrictionSection
        (k := (S1727A l).Fmod) (K := (S1727A l).K)).lift :=
  SourceArithmeticPrelude.selectedPlaces_eq_range _

/-- The selected set is the selected set of the canonical restriction section. -/
theorem S1727Layer_selectedPlaces :
    (SourceArithmeticPrelude.canonical (S1727A l)).selectedPlaces =
      (NumberFieldPlace.restrictionSection
        (k := (S1727A l).Fmod) (K := (S1727A l).K)).selected :=
  SourceArithmeticPrelude.canonical_selectedPlaces _

/-- The section map is the actual place restriction, not an arbitrary map. -/
theorem S1727Layer_sectionMap_apply (v : (S1727Layer l).valuationCarrier) :
    (S1727Layer l).sectionMap v =
      NumberFieldPlace.comap (k := (S1727A l).Fmod) v.1 :=
  valuationSectionMap_eq_comap (SourceArithmeticPrelude.canonical (S1727A l)) v

/-- With the modification field resolved: the section map is restriction of
places from F' to ℚ. -/
theorem S1727Layer_sectionMap_apply_rat (v : (S1727Layer l).valuationCarrier) :
    (S1727Layer l).sectionMap v = NumberFieldPlace.comap (k := ℚ) v.1 :=
  valuationSectionMap_eq_comap (SourceArithmeticPrelude.canonical (S1727A l)) v

/-- The right inverse is the actual place lift, not an arbitrary map. -/
theorem S1727Layer_sectionRightInverse_apply
    (w : (S1727Layer l).modifiedValuationCarrier) :
    ((S1727Layer l).sectionRightInverse w).1 =
      (SourceArithmeticPrelude.canonical (S1727A l)).placeSection.lift w :=
  valuationSectionRightInverse_apply (SourceArithmeticPrelude.canonical (S1727A l)) w

/-- Round trip V -> V_mod -> V: the lift of the restriction of a selected place
is the place itself. -/
theorem S1727Layer_section_left_inverse (v : (S1727Layer l).valuationCarrier) :
    (S1727Layer l).sectionRightInverse ((S1727Layer l).sectionMap v) = v :=
  (S1727Layer l).section_left_inverse v

/-- Round trip V_mod -> V -> V_mod: the restriction of the lift of a place is
the place itself. -/
theorem S1727Layer_section_right_inverse
    (w : (S1727Layer l).modifiedValuationCarrier) :
    (S1727Layer l).sectionMap ((S1727Layer l).sectionRightInverse w) = w :=
  (S1727Layer l).section_right_inverse w

/-- The actual place restriction is bijective; this is the Definition 3.1(e)
section property. -/
theorem S1727Layer_sectionMap_bijective :
    Function.Bijective (S1727Layer l).sectionMap :=
  valuationSectionMap_bijective (SourceArithmeticPrelude.canonical (S1727A l))

/-- The actual place lift is bijective. -/
theorem S1727Layer_sectionRightInverse_bijective :
    Function.Bijective (S1727Layer l).sectionRightInverse :=
  valuationSectionRightInverse_bijective
    (SourceArithmeticPrelude.canonical (S1727A l))

/-! ## 3. The six place-section fields, assembled item by item -/

/-- The six place-section fields of 'SourceSectionClause' as a record: the
exact D7a half. -/
structure S1727PlaceSection where
  valuationCarrier : Type
  modifiedValuationCarrier : Type
  sectionMap : valuationCarrier → modifiedValuationCarrier
  sectionRightInverse : modifiedValuationCarrier → valuationCarrier
  section_left_inverse : ∀ x, sectionRightInverse (sectionMap x) = x
  section_right_inverse : ∀ y, sectionMap (sectionRightInverse y) = y

/-- The place-section prefix of any D7 clause. -/
def S1727ClausePrefix (S : SourceSectionClause.{0, 0, 0}) : S1727PlaceSection where
  valuationCarrier := S.valuationCarrier
  modifiedValuationCarrier := S.modifiedValuationCarrier
  sectionMap := S.sectionMap
  sectionRightInverse := S.sectionRightInverse
  section_left_inverse := S.section_left_inverse
  section_right_inverse := S.section_right_inverse

/-- The actual place-section prefix determined by the canonical layer of A. -/
def S1727LayerPrefix : S1727PlaceSection where
  valuationCarrier := (S1727Layer l).valuationCarrier
  modifiedValuationCarrier := (S1727Layer l).modifiedValuationCarrier
  sectionMap := (S1727Layer l).sectionMap
  sectionRightInverse := (S1727Layer l).sectionRightInverse
  section_left_inverse := (S1727Layer l).section_left_inverse
  section_right_inverse := (S1727Layer l).section_right_inverse

/-- **The D7 clause over A.**  The six place-section fields are assigned one by
one from the canonical layer of A; the local-group and place-data fields are
exactly the D7b supply.  Nothing S1280-specific is used: this is the generic
16-slot assembly over A with the canonical layer. -/
def S1727SectionClause (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    SourceSectionClause.{0, 0, 0} where
  valuationCarrier := (S1727Layer l).valuationCarrier
  modifiedValuationCarrier := (S1727Layer l).modifiedValuationCarrier
  localGroupCarrier := G.localGroupCarrier
  modifiedLocalGroupCarrier := G.modifiedLocalGroupCarrier
  sectionMap := (S1727Layer l).sectionMap
  sectionRightInverse := (S1727Layer l).sectionRightInverse
  section_left_inverse := (S1727Layer l).section_left_inverse
  section_right_inverse := (S1727Layer l).section_right_inverse
  localGroupSection := G.localGroupSection
  localGroupSection_injective := G.localGroupSection_injective
  localGroupSection_surjective := G.localGroupSection_surjective
  finitePlaceData := G.finitePlaceData
  finitePlaceData_proved := G.finitePlaceData_proved
  infinitePlaceData := G.infinitePlaceData
  infinitePlaceData_proved := G.infinitePlaceData_proved

/-- The field-by-field assembly is definitionally the generic bridge
'd7SectionLayerBridge' of 'SourceDefinition31D4D9Supply'. -/
theorem S1727SectionClause_eq_bridge
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    S1727SectionClause l G = d7SectionLayerBridge (S1727Layer l) G := rfl

@[simp] theorem S1727SectionClause_valuationCarrier
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).valuationCarrier =
      (S1727Layer l).valuationCarrier := rfl

@[simp] theorem S1727SectionClause_modifiedValuationCarrier
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).modifiedValuationCarrier =
      (S1727Layer l).modifiedValuationCarrier := rfl

@[simp] theorem S1727SectionClause_sectionMap
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).sectionMap = (S1727Layer l).sectionMap := rfl

@[simp] theorem S1727SectionClause_sectionRightInverse
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).sectionRightInverse =
      (S1727Layer l).sectionRightInverse := rfl

@[simp] theorem S1727SectionClause_section_left_inverse
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).section_left_inverse =
      (S1727Layer l).section_left_inverse := rfl

@[simp] theorem S1727SectionClause_section_right_inverse
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).section_right_inverse =
      (S1727Layer l).section_right_inverse := rfl

@[simp] theorem S1727SectionClause_localGroupCarrier
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).localGroupCarrier = G.localGroupCarrier := rfl

@[simp] theorem S1727SectionClause_modifiedLocalGroupCarrier
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).modifiedLocalGroupCarrier =
      G.modifiedLocalGroupCarrier := rfl

@[simp] theorem S1727SectionClause_localGroupSection
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).localGroupSection = G.localGroupSection := rfl

@[simp] theorem S1727SectionClause_localGroupSection_injective
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).localGroupSection_injective =
      G.localGroupSection_injective := rfl

@[simp] theorem S1727SectionClause_localGroupSection_surjective
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).localGroupSection_surjective =
      G.localGroupSection_surjective := rfl

@[simp] theorem S1727SectionClause_finitePlaceData
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).finitePlaceData = G.finitePlaceData := rfl

@[simp] theorem S1727SectionClause_infinitePlaceData
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).infinitePlaceData = G.infinitePlaceData := rfl

/-- The place-section prefix of the constructed clause is literally the actual
prefix of the canonical layer. -/
theorem S1727SectionClause_prefix
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    S1727ClausePrefix (S1727SectionClause l G) = S1727LayerPrefix l := rfl

/-- The six place-section fields do not depend on the D7b supply: for any two
supplies the clause prefixes coincide.  This is the formal statement that the
D7a half is actual and complete while D7b is the only remaining input. -/
theorem S1727SectionClause_prefix_independent
    (G₁ G₂ : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    S1727ClausePrefix (S1727SectionClause l G₁) =
      S1727ClausePrefix (S1727SectionClause l G₂) := rfl

/-- The clause's upstairs carrier is the actual selected place set of F'. -/
theorem S1727SectionClause_valuationCarrier_eq
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).valuationCarrier =
      {v : NumberFieldPlace S1720Field //
        v ∈ (SourceArithmeticPrelude.canonical (S1727A l)).selectedPlaces} := rfl

/-- The clause's downstairs carrier is the actual place carrier of ℚ. -/
theorem S1727SectionClause_modifiedValuationCarrier_eq
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727SectionClause l G).modifiedValuationCarrier = NumberFieldPlace ℚ := rfl

/-- The actual place restriction of the clause is bijective. -/
theorem S1727SectionClause_sectionMap_bijective
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    Function.Bijective (S1727SectionClause l G).sectionMap :=
  S1727Layer_sectionMap_bijective l

/-- The clause satisfies the left round trip of Definition 3.1(e). -/
theorem S1727SectionClause_section_left
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l))
    (v : (S1727SectionClause l G).valuationCarrier) :
    (S1727SectionClause l G).sectionRightInverse
      ((S1727SectionClause l G).sectionMap v) = v :=
  (S1727SectionClause l G).section_left_inverse v

/-- The clause satisfies the right round trip of Definition 3.1(e). -/
theorem S1727SectionClause_section_right
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l))
    (w : (S1727SectionClause l G).modifiedValuationCarrier) :
    (S1727SectionClause l G).sectionMap
      ((S1727SectionClause l G).sectionRightInverse w) = w :=
  (S1727SectionClause l G).section_right_inverse w

/-- The pointwise local-group section of the clause is bijective, as supplied
by D7b. -/
theorem S1727SectionClause_localGroupSection_bijective
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l))
    (x : (S1727SectionClause l G).valuationCarrier) :
    Function.Bijective ((S1727SectionClause l G).localGroupSection x) :=
  ⟨(S1727SectionClause l G).localGroupSection_injective x,
    (S1727SectionClause l G).localGroupSection_surjective x⟩

/-! ## 4. D7b: the exact first missing structure and its first field -/

/-- **The exact first missing object of D7 over A**: the D7b local-group supply
over the canonical place-section layer.  It is not constructed here: its
content needs the actual orbicurves and their etale fundamental groups (D6). -/
abbrev S1727SectionFirstMissing : Type 1 :=
  D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)

/-- The exact first field of the clause that A does not determine: the
local-group carrier family 'V -> Type', the first ray of the curve-side
Pi_Xv / Pi_Cv data.  It is not an arithmetic local Galois group. -/
abbrev S1727D7FirstField : Type 1 :=
  (S1727Layer l).valuationCarrier → Type

/-- The first field of any D7b supply. -/
def S1727D7FirstFieldOfSupply (G : S1727SectionFirstMissing l) :
    S1727D7FirstField l :=
  G.localGroupCarrier

/-- A D7b supply determines its first field. -/
theorem S1727D7FirstField_needed (G : S1727SectionFirstMissing l) :
    Nonempty (S1727D7FirstField l) :=
  ⟨S1727D7FirstFieldOfSupply l G⟩

/-- Everything in 'D7LocalGroupSectionSupply' after the first field
'localGroupCarrier'. -/
structure S1727D7Tail (G0 : S1727D7FirstField l) where
  /-- Local group of C_K at each modified place. -/
  modifiedLocalGroupCarrier : (S1727Layer l).modifiedValuationCarrier → Type
  /-- The pointwise transport of local groups along the section map. -/
  localGroupSection : ∀ x, G0 x →
    modifiedLocalGroupCarrier ((S1727Layer l).sectionMap x)
  localGroupSection_injective : ∀ x, Function.Injective (localGroupSection x)
  localGroupSection_surjective : ∀ x, Function.Surjective (localGroupSection x)
  /-- Clause (e) place-data content (finite places). -/
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  /-- Clause (e) place-data content (infinite places). -/
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

/-- Exact decomposition of the D7b intake into its first field and its tail. -/
def S1727D7SupplyEquiv :
    S1727SectionFirstMissing l ≃
      Σ G0 : S1727D7FirstField l, S1727D7Tail l G0 where
  toFun G :=
    ⟨G.localGroupCarrier,
      { modifiedLocalGroupCarrier := G.modifiedLocalGroupCarrier
        localGroupSection := G.localGroupSection
        localGroupSection_injective := G.localGroupSection_injective
        localGroupSection_surjective := G.localGroupSection_surjective
        finitePlaceData := G.finitePlaceData
        finitePlaceData_proved := G.finitePlaceData_proved
        infinitePlaceData := G.infinitePlaceData
        infinitePlaceData_proved := G.infinitePlaceData_proved }⟩
  invFun p :=
    { localGroupCarrier := p.1
      modifiedLocalGroupCarrier := p.2.modifiedLocalGroupCarrier
      localGroupSection := p.2.localGroupSection
      localGroupSection_injective := p.2.localGroupSection_injective
      localGroupSection_surjective := p.2.localGroupSection_surjective
      finitePlaceData := p.2.finitePlaceData
      finitePlaceData_proved := p.2.finitePlaceData_proved
      infinitePlaceData := p.2.infinitePlaceData
      infinitePlaceData_proved := p.2.infinitePlaceData_proved }
  left_inv G := by cases G; rfl
  right_inv p := by rcases p with ⟨G0, t⟩; cases t; rfl

@[simp] theorem S1727D7SupplyEquiv_fst (G : S1727SectionFirstMissing l) :
    (S1727D7SupplyEquiv l G).1 = G.localGroupCarrier := rfl

/-- Nonemptiness of D7b is exactly first field plus tail. -/
theorem S1727SectionFirstMissing_nonempty_iff_firstField_tail :
    Nonempty (S1727SectionFirstMissing l) ↔
      ∃ G0 : S1727D7FirstField l, Nonempty (S1727D7Tail l G0) := by
  constructor
  · rintro ⟨G⟩
    exact ⟨G.localGroupCarrier, ⟨(S1727D7SupplyEquiv l G).2⟩⟩
  · rintro ⟨G0, ⟨t⟩⟩
    exact ⟨(S1727D7SupplyEquiv l).symm ⟨G0, t⟩⟩

/-- The first missing field of the clause is exactly the first D7b field. -/
theorem S1727SectionClause_firstMissingField
    (G : S1727SectionFirstMissing l) :
    (S1727SectionClause l G).localGroupCarrier =
      S1727D7FirstFieldOfSupply l G := rfl

/-! ## 5. Exactness: no S1280-specific constructor; the canonical-layer slice
of the clause type is exactly D7b -/

/-- The place-section layer determined by any 'SourceSectionClause.{0, 0, 0}'. -/
def S1727LayerOfClause (S : SourceSectionClause.{0, 0, 0}) :
    SourceValuationSectionLayer (S1727A l) where
  valuationCarrier := S.valuationCarrier
  modifiedValuationCarrier := S.modifiedValuationCarrier
  sectionMap := S.sectionMap
  sectionRightInverse := S.sectionRightInverse
  section_left_inverse := S.section_left_inverse
  section_right_inverse := S.section_right_inverse

/-- The D7b supply determined by any 'SourceSectionClause.{0, 0, 0}', over the
layer of its own place-section fields. -/
def S1727SupplyOfClause (S : SourceSectionClause.{0, 0, 0}) :
    D7LocalGroupSectionSupply.{0, 0} (S1727LayerOfClause l S) where
  localGroupCarrier := S.localGroupCarrier
  modifiedLocalGroupCarrier := S.modifiedLocalGroupCarrier
  localGroupSection := S.localGroupSection
  localGroupSection_injective := S.localGroupSection_injective
  localGroupSection_surjective := S.localGroupSection_surjective
  finitePlaceData := S.finitePlaceData
  finitePlaceData_proved := S.finitePlaceData_proved
  infinitePlaceData := S.infinitePlaceData
  infinitePlaceData_proved := S.infinitePlaceData_proved

/-- **No S1280-specific constructor.**  Every 'SourceSectionClause.{0, 0, 0}' is
literally the generic assembly of its own six place-section fields and its own
local-group data.  Hence constructing the D7 clause only requires the place
section (D7a, actual here) and the D7b supply, independently of the S1280
instance. -/
theorem S1727Clause_reconstruct (S : SourceSectionClause.{0, 0, 0}) :
    d7SectionLayerBridge (S1727LayerOfClause l S) (S1727SupplyOfClause l S) = S := by
  cases S
  rfl

/-- Clauses are exactly pairs (place-section layer, D7b supply). -/
abbrev S1727ClauseDecomposition : Type 1 :=
  Sigma fun M : SourceValuationSectionLayer (S1727A l) =>
    D7LocalGroupSectionSupply.{0, 0} M

/-- The exact decomposition of the D7 clause type. -/
def S1727ClauseDecompositionEquiv :
    S1727ClauseDecomposition l ≃ SourceSectionClause.{0, 0, 0} where
  toFun p := d7SectionLayerBridge p.1 p.2
  invFun S := ⟨S1727LayerOfClause l S, S1727SupplyOfClause l S⟩
  left_inv p := by
    rcases p with ⟨M, G⟩
    rfl
  right_inv S := S1727Clause_reconstruct l S

/-- The clauses whose place-section layer is the canonical layer of A. -/
abbrev S1727CanonicalFiber : Type 1 :=
  {p : S1727ClauseDecomposition l // p.1 = S1727Layer l}

/-- **The exact sense in which D7b is an explicit input.**  The clauses whose
place-section layer is the canonical layer over A are exactly the D7b supplies
over that layer: the arithmetic input and its canonical place section determine
the six D7a fields and nothing more. -/
def S1727CanonicalFiberEquiv :
    S1727CanonicalFiber l ≃ D7LocalGroupSectionSupply.{0, 0} (S1727Layer l) where
  toFun p := p.2 ▸ p.1.2
  invFun G := ⟨⟨S1727Layer l, G⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨M, G⟩, h⟩
    cases h
    rfl
  right_inv G := rfl

/-- The fiber equivalence sends the canonical-layer supply to its clause. -/
theorem S1727CanonicalFiberEquiv_fiber (G : S1727SectionFirstMissing l) :
    S1727CanonicalFiberEquiv l ⟨⟨S1727Layer l, G⟩, rfl⟩ = G := rfl

/-- Nonemptiness of the canonical-layer slice is exactly nonemptiness of D7b. -/
theorem S1727CanonicalFiber_nonempty_iff :
    Nonempty (S1727CanonicalFiber l) ↔
      Nonempty (S1727SectionFirstMissing l) :=
  ⟨fun ⟨p⟩ => ⟨S1727CanonicalFiberEquiv l p⟩,
    fun ⟨G⟩ => ⟨(S1727CanonicalFiberEquiv l).symm G⟩⟩

/-! ## 6. Consumer: filling the D7 slot of a source contract -/

/-- Fill the 'sections' (D7) slot of a source contract with the clause over the
actual arithmetic input A.  The rest of the contract is untouched. -/
def S1727FillD7 (S : SourceDefinition31Data.{0} l)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    SourceDefinition31Data.{0} l :=
  { S with sections := S1727SectionClause l G }

@[simp] theorem S1727FillD7_sections (S : SourceDefinition31Data.{0} l)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1727Layer l)) :
    (S1727FillD7 l S G).sections = S1727SectionClause l G := rfl

/-! ## 7. Axiom footprint -/

#print axioms S1727A_Fmod
#print axioms S1727A_F
#print axioms S1727A_K
#print axioms S1727Layer
#print axioms S1727Layer_sectionMap_apply
#print axioms S1727Layer_sectionMap_bijective
#print axioms S1727Layer_sectionRightInverse_bijective
#print axioms S1727SectionClause
#print axioms S1727SectionClause_eq_bridge
#print axioms S1727SectionClause_prefix
#print axioms S1727SectionClause_prefix_independent
#print axioms S1727SectionClause_sectionMap_bijective
#print axioms S1727D7SupplyEquiv
#print axioms S1727SectionFirstMissing_nonempty_iff_firstField_tail
#print axioms S1727SectionClause_firstMissingField
#print axioms S1727Clause_reconstruct
#print axioms S1727ClauseDecompositionEquiv
#print axioms S1727CanonicalFiberEquiv
#print axioms S1727CanonicalFiberEquiv_fiber
#print axioms S1727CanonicalFiber_nonempty_iff
#print axioms S1727FillD7

end LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual

end

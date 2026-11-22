import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31PlacePartition
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31LocalValuationSections
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31ArithmeticCompatibilitySlots
import Mathlib.Algebra.Group.ULift

/-!
# IUT I Definition 3.1(b)-(f): the D4-D9 supply interface

Consumer: `SourceDefinition31Data.toInitialThetaInput` ->
`InitialThetaInput` (Theorem 3.11 input chain, items 22-31). This module
names the supply interface of the D4-D9 slots of `SourceDefinition31Data`
(`SourceDefinition31Boundary.lean`), so that the clause values are always
assembled from explicitly named source-side input layers, never
manufactured.

Per-item summary (paper anchors are extraction lines of
`papers/motizuki_corpus/text/Inter-universal Teichmuller Theory I.txt`):

* D4 `D4ReductionSupply` (Definition 3.1(b)-(c), lines 3131-3184): three
  frozen layers - the three reduction cards, the clause (c) coprimality
  cards, and the bad-place Tate-uniformization identification card; the
  reduction clause itself is the existing assembly
  `toSourceReductionClause` (`SourcePlacePartitionReduction.lean`).
* D5 `D5TorsionSupply` (Definition 3.1(c), lines 3176-3184): the frozen
  `TorsionCarrierReduction.SourceTorsionDatum` (rank-two `l`-torsion
  basis; literal `SL_2(F_l)` containment as a source-satisfaction
  hypothesis; `K` as the kernel field), together with the supplied
  six-torsion-independence and `l`-compatibility source conditions; the
  bridge `toTorsionClause` builds `SourceTorsionClause` with the
  semantics-backed `LargeImageContainsSL2` image component; the range
  group of the canonical representation is lifted to `Type u` (`ULift`)
  to match the clause's `representationGroup` universe slot.
* D6 (Definition 3.1(d), lines 3185-3215): no new record; the intake is
  the boundary clause itself. Conditional constructors from an actual
  orbicurve with certified etale fundamental groups live in
  `SourceClauseConstructors.lean` (`SourceOrbicurveGroupData.ofFundamentalGroup`,
  `exactSequenceOfFundamentalGroup`); the concrete orbicurve still has to
  be supplied. Recorded as `sourceDefinition31D6Supply`.
* D7 (Definition 3.1(e), lines 3216-3272): split into D7a
  (place-section half) and D7b (local-group half). D7a is absorbed from
  the cross-line module `SourceDefinition31LocalValuationSections.lean`
  (now imported; `SourceValuationSectionLayer.canonical` constructs the
  place-section layer for every arithmetic input, unconditionally) and
  wired into the D7 gate: `D7aPlaceSectionConstruction` /
  `d7aPlaceSectionConstruction_proved`, the 16-slot assembly
  `d7SectionLayerBridge`, the reduction
  `d7SectionConstruction_of_localGroupSupply` (universe instance
  `v := u`, no `ULift`), and the `d11EntryData` section-slot weld
  `d11EntryData_sections_bridge`. D7b (local-group carriers, pointwise
  bijective section, place data) stays an explicit conditional intake
  `D7LocalGroupSectionSupply`, keyed to D6. Recorded as
  `sourceDefinition31D7aPlaceSection` / `sourceDefinition31D7bLocalGroup`.
* D8 (Definition 3.1(f), lines 3273-3295): conditional boundary-origin
  constructors live in `SourceClauseConstructors.lean`
  (`canonicalKQuotientData`, `ofCanonicalKBoundaryOrigin`,
  `ofCanonicalBoundaryData`); the cusp origin from the nonzero quotient
  element remains a source input. Recorded as `sourceDefinition31D8Supply`.
* D9 `D9CompatibilitySupply` (Definition 3.1(a)-(f)): the five arithmetic
  compatibility (Prop, proof) pairs stay supplied by the instance author;
  the pair is packed, bundled and projected here, never manufactured.
  Four of the five slots now have a wiring constructor
  (`D9CompatibilitySupply.ofArithmeticSlots`) assembled from the concrete
  slot statements of `SourceDefinition31ArithmeticCompatibilitySlots.lean`;
  the orbicurve slot remains an explicit source supply (parked card).

The bundle `D4D9Supply` assembles `SourceDefinition31Data` through the
existing entry `d11EntryData` (same file family), and the gates
`D5TorsionConstruction` and `D9/D10` reduce to nonemptiness of the
supply. No field of any clause is weakened; conditional supply is never
stated as unconditional.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe u v w

noncomputable section

namespace InitialThetaSource

namespace Definition31D4D9Supply

open PlacePartitionReduction

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-! ## D4: the reduction and q-parameter supply -/

/-- The frozen D4 supply for a supplied bad-moduli selection: the three
reduction cards, the clause (c) coprimality cards, and the bad-place
Tate-uniformization identification card. All three components are
source-side hypotheses; none is manufactured here. -/
structure D4ReductionSupply (P : SourcePlaceSelection A) where
  /-- Stable/multiplicative/split reduction cards over every bad fibre. -/
  reduction : BadPlaceReductionCards P
  /-- Clause (c) coprimalities: bad residue characteristics and
  q-parameter orders are prime to `l`. -/
  qParameter : BadPlaceQParameterCards P
  /-- The per-place Tate identification card (q-candidate, comparison,
  order coprimality). -/
  tateUniformization : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P

/-- The D4 supply assembles the reduction clause through the existing
assembly `toSourceReductionClause`. -/
noncomputable def D4ReductionSupply.toReductionClause
    (S : D4ReductionSupply (A := A) P) [Fintype (Bad P)] :
    Theorem311Source.SourceReductionClause (Selected P) (Bad P) :=
  toSourceReductionClause P S.reduction

/-- The assembled q-parameter is the completed-DVR proxy; its
identification with the Tate `q`-parameter is the recorded boundary (the
Tate card is the supply-side witness of that boundary). -/
theorem D4ReductionSupply.toReductionClause_qParameter
    (S : D4ReductionSupply (A := A) P) [Fintype (Bad P)] :
    (S.toReductionClause).qParameter = badPlaceQProxy P :=
  rfl

/-! ## D5: the torsion, Galois representation, and large-image supply -/

/-- The frozen D5 supply: the `SourceTorsionDatum` of
`SourceTorsionCarrierReduction` (rank-two basis, literal `SL_2`
containment, kernel-field identification) plus the source-side torsion
carrier data and the two remaining clause-(c) source conditions. -/
structure D5TorsionSupply (l : PrimeGeFive)
    (A : InitialThetaArithmeticData.{u} l) where
  /-- Rank-two basis, large-image containment, kernel-field
  identification. -/
  datum : TorsionCarrierReduction.SourceTorsionDatum l A
  /-- Source carrier of the six labelled torsion slots. -/
  torsionCarrier : Type u
  [torsionCarrierLaw : Group torsionCarrier]
  /-- The six-slot labelling of the carrier. -/
  torsionLabel : torsionCarrier → Fin 6
  torsionNonempty : Nonempty torsionCarrier
  /-- Six-torsion independence (source condition). -/
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  /-- `l`-compatibility with the q-parameters (source condition). -/
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

attribute [instance] D5TorsionSupply.torsionCarrierLaw

/-- The D5 bridge: the frozen datum fixes the canonical representation
`G_F -> GL_2(F_l)` and its surjection onto its range; the range group is
lifted to `Type u` (`ULift`) because the clause's `representationGroup`
slot is universe-`u` while the range of the `ZMod l`-valued
representation lives in `Type 0`. The image component is the
semantics-backed `LargeImageContainsSL2` (equivalent to the literal
containment by `largeImageSL2_iff_forall`); the remaining clause fields
are the supplied source conditions. -/
noncomputable def D5TorsionSupply.toTorsionClause (S : D5TorsionSupply l A) :
    Theorem311Source.SourceTorsionClause l where
  torsionCarrier := S.torsionCarrier
  torsionCarrierLaw := inferInstance
  torsionLabel := S.torsionLabel
  torsionNonempty := S.torsionNonempty
  representationCarrier := SourceAbsoluteGalois A
  representationCarrierLaw := inferInstance
  representationGroup := ULift.{u} S.datum.representation.range
  representationGroupLaw := inferInstance
  representation :=
    (MulEquiv.ulift.symm :
      S.datum.representation.range ≃* ULift.{u} S.datum.representation.range).toMonoidHom.comp
      S.datum.representation.rangeRestrict
  representation_surjective := fun y => by
    cases y with
    | up a =>
      obtain ⟨sigma, hsigma⟩ :=
        S.datum.representation.rangeRestrict_surjective a
      exact ⟨sigma, congrArg ULift.up hsigma⟩
  imageContainsSL2 := TorsionCarrierReduction.LargeImageContainsSL2 S.datum.representation
  imageContainsSL2_proved := S.datum.image_contains_SL2_forall
  sixTorsionIndependent := S.sixTorsionIndependent
  sixTorsionIndependent_proved := S.sixTorsionIndependent_proved
  lTorsionCompatible := S.lTorsionCompatible
  lTorsionCompatible_proved := S.lTorsionCompatible_proved

/-- The image component of the bridged clause is the semantics-backed
`LargeImageContainsSL2` of the frozen datum representation. -/
theorem D5TorsionSupply.toTorsionClause_imageContainsSL2
    (S : D5TorsionSupply l A) :
    S.toTorsionClause.imageContainsSL2 =
      TorsionCarrierReduction.LargeImageContainsSL2 S.datum.representation :=
  rfl

/-! ## D9: the five arithmetic compatibility pairs -/

/-- The five arithmetic compatibility slots as supplied (Prop, proof)
pairs; the concrete content of each Proposition is the instance author's
choice and is not fixed or weakened here. -/
structure D9CompatibilitySupply where
  reduction : Prop
  reduction_proved : reduction
  torsion : Prop
  torsion_proved : torsion
  orbicurve : Prop
  orbicurve_proved : orbicurve
  sections : Prop
  sections_proved : sections
  cusp : Prop
  cusp_proved : cusp

/-- The five supplied compatibility pairs, bundled. -/
theorem D9CompatibilitySupply.bundle (S : D9CompatibilitySupply) :
    S.reduction ∧ S.torsion ∧ S.orbicurve ∧ S.sections ∧ S.cusp :=
  ⟨S.reduction_proved, S.torsion_proved, S.orbicurve_proved,
    S.sections_proved, S.cusp_proved⟩

/-- The D9 five-slot supply wired to the concrete arithmetic slot content
of `SourceDefinition31ArithmeticCompatibilitySlots`: the reduction,
torsion, sections, and cusp slots are the named statements proved there
from the supplied cards and clauses; the orbicurve slot remains an
explicit source supply (parked card
`IUT-I.definition-3.1-D9-orbicurve-slot`). -/
def D9CompatibilitySupply.ofArithmeticSlots
    (P : SourcePlaceSelection A) [Fintype (Bad P)]
    (C : BadPlaceReductionCards P) (Q : BadPlaceQParameterCards P)
    {T : Theorem311Source.SourceTorsionClause.{u, v, w} l}
    {X : Iut.HyperbolicOrbicurve A.K}
    (O : TorsionQuotientBoundaryOrigin l A X)
    (orbicurve : Prop) (orbicurve_proved : orbicurve) :
    D9CompatibilitySupply where
  reduction := ArithmeticReductionCompatibility P C Q
  reduction_proved := arithmeticReductionCompatibility_of_supply P C Q
  torsion := ArithmeticTorsionCompatibility T
  torsion_proved := arithmeticTorsionCompatibility_of_clause T
  orbicurve := orbicurve
  orbicurve_proved := orbicurve_proved
  sections := ArithmeticSectionCompatibility P
  sections_proved := arithmeticSectionCompatibility_canonical P
  cusp := ArithmeticCuspOriginCompatibility O
  cusp_proved := arithmeticCuspOriginCompatibility_of_supply O

/-! ## The D4-D9 bundle and its assembly into the source contract -/

/-- The D4-D9 supply bundle for a supplied bad-moduli selection, the
three boundary clause records (D6/D7/D8 intakes are those records
themselves), and the five compatibility pairs. -/
structure D4D9Supply (A : InitialThetaArithmeticData.{u} l) where
  selection : SourcePlaceSelection A
  [badFinite : Fintype (Bad selection)]
  d4 : D4ReductionSupply selection
  d5 : D5TorsionSupply l A
  orbicurve : Theorem311Source.SourceOrbicurveClause
  sections : Theorem311Source.SourceSectionClause
  cusp : Theorem311Source.SourceCuspClause
  compatibility : D9CompatibilitySupply

/-- The bundle assembles `SourceDefinition31Data` through the existing
D11-E entry `d11EntryData`; every component is the supplied one. -/
noncomputable def D4D9Supply.toSourceData (S : D4D9Supply A) :
    Theorem311Source.SourceDefinition31Data.{u} l :=
  letI : Fintype (Bad S.selection) := S.badFinite
  Definition31PlacePartition.d11EntryData S.selection S.d4.reduction
    S.d5.toTorsionClause S.orbicurve S.sections S.cusp
    S.compatibility.reduction S.compatibility.reduction_proved
    S.compatibility.torsion S.compatibility.torsion_proved
    S.compatibility.orbicurve S.compatibility.orbicurve_proved
    S.compatibility.sections S.compatibility.sections_proved
    S.compatibility.cusp S.compatibility.cusp_proved

@[simp] theorem D4D9Supply.toSourceData_selectedPlaces (S : D4D9Supply A) :
    (S.toSourceData).selectedPlaces = Selected S.selection :=
  rfl

@[simp] theorem D4D9Supply.toSourceData_badPlaces (S : D4D9Supply A) :
    (S.toSourceData).badPlaces = Bad S.selection :=
  rfl

@[simp] theorem D4D9Supply.toSourceData_reduction (S : D4D9Supply A) :
    (S.toSourceData).reduction =
      @toSourceReductionClause _ _ S.selection S.badFinite S.d4.reduction :=
  rfl

@[simp] theorem D4D9Supply.toSourceData_torsion (S : D4D9Supply A) :
    (S.toSourceData).torsion = S.d5.toTorsionClause :=
  rfl

/-- Consumer-chain spec: the arithmetic component of the Theorem 3.11
input chain is the bundle's arithmetic input. -/
theorem D4D9Supply.toSourceData_toInitialThetaInput_arithmetic
    (S : D4D9Supply A) :
    (S.toSourceData).toInitialThetaInput.arithmetic = A :=
  rfl

/-- Consumer-chain spec: the bad-place index of the Theorem 3.11 input
chain is exactly the selection's `V^bad_mod` subtype. -/
theorem D4D9Supply.toSourceData_toInitialThetaInput_badPlaces
    (S : D4D9Supply A) :
    (S.toSourceData).toInitialThetaInput.badPlaces = Bad S.selection :=
  rfl

/-! ## Gate reductions -/

/-- The D5 gate reduces to nonemptiness of the frozen supply: the bridge
`toTorsionClause` is the only construction step. -/
theorem d5TorsionConstruction_of_supplies
    (h : ∀ A : InitialThetaArithmeticData.{u} l,
      Nonempty (D5TorsionSupply l A)) :
    Theorem311Source.SourceDefinition31Root.D5TorsionConstruction.{u, u, u} l :=
  fun A => ⟨(h A).some.toTorsionClause⟩

/-- The D9 gate (five compatibility construction) reduces to
nonemptiness of the D4-D9 bundle. -/
theorem d9CompatibilityConstruction_of_supplies
    (h : ∀ A : InitialThetaArithmeticData.{u} l,
      Nonempty (D4D9Supply A)) :
    Theorem311Source.SourceDefinition31Root.D9CompatibilityConstruction.{u} l :=
  fun A => ⟨(h A).some.toSourceData⟩

/-- The D10 gate is the same quantified existence as the D9 gate at the
current interface; the bundle supplies both. -/
theorem d10InitialThetaConstruction_of_supplies
    (h : ∀ A : InitialThetaArithmeticData.{u} l,
      Nonempty (D4D9Supply A)) :
    Theorem311Source.SourceDefinition31Root.D10InitialThetaConstruction.{u} l :=
  fun A => ⟨(h A).some.toSourceData⟩

/-! ## D7 section-layer integration: place half (D7a), local-group half (D7b)

The cross-line module `SourceDefinition31LocalValuationSections.lean`
(SHA 27B21DBE80754128EBF0728234E16BFDF8B5FA01BFD7B1C85FB27C45A5BAA2B9)
proves the place-section half of Definition 3.1(e) for every arithmetic
input. This section consumes that layer: it is imported, not rebuilt; the
D7a gate is wired to `SourceValuationSectionLayer.exists_canonical`; the
16-slot `SourceSectionClause` assembly is exposed as
`d7SectionLayerBridge`; and the D7 gate `D7SectionConstruction`
(`SourceDefinition31RootLemmas.lean:5164`) is reduced to the D7b intake at
the universe instance `v := u`. No declaration of the layer module is
altered, and nothing here closes D7b. -/

/-- D7b intake: the local-group half of the D7 clause (Definition 3.1(e),
lines 3220-3272) - the local-group carriers over the section carrier pair,
the pointwise bijective local-group section, and the finite/infinite place
data propositions. The intended content needs the actual orbicurves X_K,
C_K and their etale fundamental groups (D6, open): no constructor from the
arithmetic input alone is provided, so this stays an explicit supply. -/
structure D7LocalGroupSectionSupply
    (L : SourceValuationSectionLayer A) where
  /-- Local group of X_K at each place of the valuation section. -/
  localGroupCarrier : L.valuationCarrier → Type w
  /-- Local group of C_K at each place of the modified carrier. -/
  modifiedLocalGroupCarrier : L.modifiedValuationCarrier → Type w
  /-- The pointwise transport of local groups along the section map. -/
  localGroupSection : ∀ x, localGroupCarrier x →
    modifiedLocalGroupCarrier (L.sectionMap x)
  localGroupSection_injective : ∀ x,
    Function.Injective (localGroupSection x)
  localGroupSection_surjective : ∀ x,
    Function.Surjective (localGroupSection x)
  /-- Clause (e) place-data content (finite places). -/
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  /-- Clause (e) place-data content (infinite places). -/
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

/-- The 16-slot assembly: the place-section layer (D7a) supplies the
carrier pair and the section data; the D7b intake supplies the local-group
and place-data slots. Universe adjudication: the clause is instantiated at
`v := u`, so the layer's `Type u` carrier pair fills the `Type u`/`Type v`
slots directly, with no `ULift` transport; the local-group universe `w`
stays free. The layer's slots are the ones named in
`SourceDefinition31LocalValuationSections.lean` (`valuationCarrier`,
`modifiedValuationCarrier`, `sectionMap`, `sectionRightInverse`,
`section_left_inverse`, `section_right_inverse`). -/
noncomputable def d7SectionLayerBridge
    (L : SourceValuationSectionLayer A)
    (G : D7LocalGroupSectionSupply L) :
    Theorem311Source.SourceSectionClause.{u, u, w} where
  valuationCarrier := L.valuationCarrier
  modifiedValuationCarrier := L.modifiedValuationCarrier
  localGroupCarrier := G.localGroupCarrier
  modifiedLocalGroupCarrier := G.modifiedLocalGroupCarrier
  sectionMap := L.sectionMap
  sectionRightInverse := L.sectionRightInverse
  section_left_inverse := L.section_left_inverse
  section_right_inverse := L.section_right_inverse
  localGroupSection := G.localGroupSection
  localGroupSection_injective := G.localGroupSection_injective
  localGroupSection_surjective := G.localGroupSection_surjective
  finitePlaceData := G.finitePlaceData
  finitePlaceData_proved := G.finitePlaceData_proved
  infinitePlaceData := G.infinitePlaceData
  infinitePlaceData_proved := G.infinitePlaceData_proved

/-- D7a half of the D7 gate: the place-section layer exists for every
arithmetic input. This wires the imported cross-line theorem
`SourceValuationSectionLayer.exists_canonical` (Mendel module, SHA
27B21DBE...); the layer itself is not rebuilt here. -/
def D7aPlaceSectionConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty (SourceValuationSectionLayer A)

/-- D7a is closed unconditionally by the imported canonical layer. -/
theorem d7aPlaceSectionConstruction_proved (l : PrimeGeFive) :
    D7aPlaceSectionConstruction.{u} l :=
  SourceValuationSectionLayer.exists_canonical l

/-- D7b half of the D7 gate: a D7 local-group intake for the canonical
place-section layer of every arithmetic input. Keyed to D6: the intended
content (the local group of X_K inside that of C_K at each place) needs
the actual orbicurves; no arithmetic-input constructor is provided. -/
def D7bLocalGroupSectionConstruction (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    Nonempty (D7LocalGroupSectionSupply.{u, w}
      (SourceValuationSectionLayer.canonical A))

/-- The D7 gate `D7SectionConstruction`
(`SourceDefinition31RootLemmas.lean:5164`) reduces, at the universe
instance `v := u`, to the D7b intake alone: D7a is closed by
`d7aPlaceSectionConstruction_proved`, so only the local-group supply
remains a hypothesis. -/
theorem d7SectionConstruction_of_localGroupSupply
    (h : D7bLocalGroupSectionConstruction.{u, w} l) :
    Theorem311Source.SourceDefinition31Root.D7SectionConstruction.{u, u, w} l :=
  fun A => ⟨d7SectionLayerBridge (SourceValuationSectionLayer.canonical A)
    (h A).some⟩

/-- The D11-E entry `d11EntryData` (`SourceDefinition31PlacePartition.lean:180`)
consumes the bridge product as its `Se` parameter: the section slot of the
assembled `SourceDefinition31Data` is exactly the 16-slot bridge product
(the seam is definitional; no further obligation is created). -/
theorem d11EntryData_sections_bridge
    (P : SourcePlaceSelection A) [Fintype (Bad P)]
    (C : BadPlaceReductionCards P)
    (T : Theorem311Source.SourceTorsionClause l)
    (O : Theorem311Source.SourceOrbicurveClause)
    (L : SourceValuationSectionLayer A)
    (G : D7LocalGroupSectionSupply L)
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (Definition31PlacePartition.d11EntryData P C T O
        (d7SectionLayerBridge L G) Cu
        redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).sections =
      d7SectionLayerBridge L G :=
  rfl

end Definition31D4D9Supply

end InitialThetaSource

namespace Audit

/-- D4 supply card: the reduction/q-parameter intake layer. -/
def sourceDefinition31D4Supply : Obligation :=
  { id := "IUT-I.definition-3.1-D4-supply"
    source := "IUT I, Definition 3.1(b)-(c) (extraction lines 3131-3184)"
    status := VerificationStatus.conditional
    note :=
      "D4 supply interface: reduction cards (stable/multiplicative/split, " ++
        "`BadPlaceReductionCards`), clause (c) coprimality cards " ++
        "(`BadPlaceQParameterCards`), and the bad-place Tate-uniformization " ++
        "identification card assemble the reduction clause through " ++
        "`toSourceReductionClause`; named intake `D4ReductionSupply` " ++
        "(`SourceDefinition31D4D9Supply.lean`). Residuals: source selection " ++
        "and finite bad index (D3 umbrella card), the F-to-Fmod bridge, and " ++
        "the boundary that the real q-proxy is the Tate q-parameter. Note on " ++
        "the gate `D4ReductionConstruction`: its arbitrary-partition " ++
        "quantifier accepts purely formal inhabitants of the record (constant " ++
        "q-parameter) with no curve link; the content-bearing quantifier is " ++
        "the selection-based supply, and the gate is not closed by any " ++
        "formal inhabitant. Consumers: D9/D10 bundle and the Theorem 3.11 " ++
        "input chain (items 22-31)."
    dependsOn :=
      [ "IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap",
        "IUT-I.definition-3.1-D4" ] }

/-- D5 supply card: the frozen-datum bridge. -/
def sourceDefinition31D5Supply : Obligation :=
  { id := "IUT-I.definition-3.1-D5-supply"
    source := "IUT I, Definition 3.1(c) (extraction lines 3176-3184)"
    status := VerificationStatus.conditional
    note :=
      "D5 supply interface `D5TorsionSupply` bridges " ++
        "`TorsionCarrierReduction.SourceTorsionDatum` (rank-two l-torsion " ++
        "basis; literal SL_2 containment as source hypothesis; K as kernel " ++
        "field) to `SourceTorsionClause` (`toTorsionClause`): the canonical " ++
        "representation is restricted onto its range (lifted by `ULift` " ++
        "to the clause's universe-`u` group slot) for surjectivity, and " ++
        "the image component is `LargeImageContainsSL2`, equivalent to the " ++
        "literal containment by `largeImageSL2_iff_forall`. The " ++
        "six-torsion-independence and l-compatibility slots remain supplied " ++
        "source conditions. `D5TorsionConstruction` reduces to supply " ++
        "nonemptiness. The deep cards stay open and are not engaged: " ++
        "`IUT-I.elliptic-l-torsion-large-image` (Serre-style statement, " ++
        "`SerreStyleLargeImageStatement`) and " ++
        "`Foundations.Geometry.elliptic-l-torsion-rank-two` " ++
        "(`RankTwoTorsionBasisGap`). No large-image theorem is proved or " ++
        "assumed."
    dependsOn :=
      [ "IUT-I.definition-3.1-D5",
        "IUT-I.definition-3.1-D4-supply" ] }

/-- D6 direction card: conditional constructors exist; the orbicurve is a
source input. -/
def sourceDefinition31D6Supply : Obligation :=
  { id := "IUT-I.definition-3.1-D6-supply"
    source := "IUT I, Definition 3.1(d) (extraction lines 3185-3215)"
    status := VerificationStatus.conditional
    note :=
      "D6 direction: the exact sequence `1 -> Delta -> Pi -> G -> 1` and " ++
        "the hyperbolic orbicurves X_K, C_K are supplied through the " ++
        "conditional constructors of `SourceClauseConstructors.lean` " ++
        "(`SourceOrbicurveGroupData.ofFundamentalGroup`, " ++
        "`exactSequenceOfFundamentalGroup`, `SourceOrbicurveFiniteEtaleCover`), " ++
        "which take an actual orbicurve with certified etale fundamental " ++
        "groups as hypotheses. No tree supplier constructs X_K, C_K over K " ++
        "from the arithmetic input alone; the D6 intake is the boundary " ++
        "clause record itself and the residual (orbicurve + certified " ++
        "groups) stays a source input. Consumer: D7 local groups, D9/D10 " ++
        "bundle."
    dependsOn :=
      [ "IUT-I.definition-3.1-D6",
        "IUT-I.definition-3.1-D5-supply" ] }

/-- D7 split card: D7a place-section supplied and wired; D7b local-group
open. -/
def sourceDefinition31D7Supply : Obligation :=
  { id := "IUT-I.definition-3.1-D7-supply"
    source := "IUT I, Definition 3.1(e) (extraction lines 3216-3272)"
    status := VerificationStatus.conditional
    note :=
      "D7 is split into D7a (place-section half) and D7b (local-group " ++
        "half). D7a is supplied and wired: the imported cross-line module " ++
        "`SourceDefinition31LocalValuationSections.lean` proves the " ++
        "canonical layer for every arithmetic input, and " ++
        "`d7SectionLayerBridge` fills the 16-slot clause slots from it " ++
        "plus the D7b intake; see `sourceDefinition31D7aPlaceSection`. " ++
        "D7b remains an explicit conditional intake keyed to D6; see " ++
        "`sourceDefinition31D7bLocalGroup`. The gate " ++
        "`D7SectionConstruction` is reduced to the D7b intake at the " ++
        "universe instance `v := u`. Consumer: D9/D10 bundle; the boundary " ++
        "clause record is the intake."
    dependsOn :=
      [ "IUT-I.definition-3.1-D7",
        "IUT-I.definition-3.1-D6-supply",
        "IUT-I.definition-3.1-D7a-place-section",
        "IUT-I.definition-3.1-D7b-local-group" ] }

/-- D7a card: the place-section half is supplied by the imported
cross-line layer and wired into the D7 gate. -/
def sourceDefinition31D7aPlaceSection : Obligation :=
  { id := "IUT-I.definition-3.1-D7a-place-section"
    source := "IUT I, Definition 3.1(e), place-section half (extraction lines 3216-3220)"
    status := VerificationStatus.provedKernel
    note :=
      "D7a: the place-section half of clause (e). The layer " ++
        "`SourceValuationSectionLayer` of " ++
        "`SourceDefinition31LocalValuationSections.lean` (SHA " ++
        "27B21DBE80754128EBF0728234E16BFDF8B5FA01BFD7B1C85FB27C45A5BAA2B9) " ++
        "is imported by `SourceDefinition31D4D9Supply.lean` (not rebuilt); " ++
        "`d7aPlaceSectionConstruction_proved` wires " ++
        "`SourceValuationSectionLayer.exists_canonical` as the D7a gate " ++
        "`D7aPlaceSectionConstruction`; `d7SectionLayerBridge` fills the " ++
        "six place-section slots of the 16-slot `SourceSectionClause` at " ++
        "the universe instance `v := u` (no `ULift` transport); and " ++
        "`d11EntryData_sections_bridge` welds the bridge product to the " ++
        "`Se` parameter of `d11EntryData`. Residual (kept out of the " ++
        "claim): the carrier choice V is one canonical admissible choice " ++
        "of the paper's input data; the deep semantics remains the " ++
        "supplied arithmetic input, and this card claims only the layer " ++
        "and the wiring. Consumer: D7b supply and the D7 gate reduction " ++
        "`d7SectionConstruction_of_localGroupSupply`."
    dependsOn :=
      [ "IUT-I.definition-3.1-D7-place-section-layer" ] }

/-- D7b card: the local-group half remains a conditional intake keyed to
D6. -/
def sourceDefinition31D7bLocalGroup : Obligation :=
  { id := "IUT-I.definition-3.1-D7b-local-group"
    source := "IUT I, Definition 3.1(e), local-group half (extraction lines 3220-3272)"
    status := VerificationStatus.conditional
    note :=
      "D7b: the local-group half of clause (e). Named intake " ++
        "`D7LocalGroupSectionSupply` (conditional): local-group carriers " ++
        "over the place-section carrier pair (`Type w`), the pointwise " ++
        "local-group section with injectivity/surjectivity, and the " ++
        "finite/infinite place-data propositions with proofs; all nine " ++
        "remaining slots of the 16-slot clause come from it via " ++
        "`d7SectionLayerBridge`. The intended content (the local group of " ++
        "X_K inside that of C_K at each place) needs the actual orbicurves " ++
        "and their etale fundamental groups, i.e. D6, which is open; no " ++
        "constructor from the arithmetic input alone is provided. The D7 " ++
        "gate `D7SectionConstruction` reduces to this intake alone at the " ++
        "universe instance `v := u` " ++
        "(`d7SectionConstruction_of_localGroupSupply`)."
    dependsOn :=
      [ "IUT-I.definition-3.1-D7-local-group-residual",
        "IUT-I.definition-3.1-D7a-place-section",
        "IUT-I.definition-3.1-D6" ] }

/-- D8 direction card: boundary-origin constructors conditional; cusp
origin is a source input. -/
def sourceDefinition31D8Supply : Obligation :=
  { id := "IUT-I.definition-3.1-D8-supply"
    source := "IUT I, Definition 3.1(f) (extraction lines 3273-3295)"
    status := VerificationStatus.conditional
    note :=
      "D8 direction: the cusp content (epsilon, cusp scale, source " ++
        "compatibility) is supplied; conditional boundary-origin " ++
        "constructors exist in `SourceClauseConstructors.lean` " ++
        "(`canonicalKQuotientData`, `ofCanonicalKBoundaryOrigin`, " ++
        "`ofCanonicalBoundaryData` with basis/cusp binding theorems), " ++
        "pending the source cusp-origin map from the nonzero quotient " ++
        "element, which stays a source input. No epsilon value is " ++
        "manufactured here. Consumer: D9/D10 bundle."
    dependsOn :=
      [ "IUT-I.definition-3.1-D8",
        "IUT-I.definition-3.1-D7-supply" ] }

/-- D9 supply card: the five compatibility pairs. -/
def sourceDefinition31D9Supply : Obligation :=
  { id := "IUT-I.definition-3.1-D9-supply"
    source := "IUT I, Definition 3.1(a)-(f)"
    status := VerificationStatus.conditional
    note :=
      "D9 supply interface `D9CompatibilitySupply`: the five arithmetic " ++
        "compatibility slots remain (Prop, proof) pairs supplied by the " ++
        "instance author; they are packed, bundled (`bundle`) and projected " ++
        "into `SourceDefinition31Data` by the D4-D9 bundle, never " ++
        "manufactured or weakened. The gates " ++
        "`D9CompatibilityConstruction` and `D10InitialThetaConstruction` " ++
        "reduce to nonemptiness of `D4D9Supply`."
    dependsOn :=
      [ "IUT-I.definition-3.1-D9",
        "IUT-I.definition-3.1-D8-supply" ] }

/-- The D4-D9 supply-interface umbrella card. -/
def sourceDefinition31D4D9SupplyInterface : Obligation :=
  { id := "IUT-I.definition-3.1-D4-D9-supply-interface"
    source := "IUT I, Definition 3.1(b)-(f); Remark 3.1.1"
    status := VerificationStatus.conditional
    note :=
      "The D4-D9 supply interface of the `SourceDefinition31Data` contract: " ++
        "`D4D9Supply` bundles the D4 `D4ReductionSupply`, the D5 " ++
        "`D5TorsionSupply`, the D6/D7/D8 boundary clause records, and the D9 " ++
        "`D9CompatibilitySupply`; `toSourceData` assembles the source record " ++
        "through the existing `d11EntryData`, and the consumer chain " ++
        "`toInitialThetaInput` (Theorem 3.11 items 22-31) is exposed by " ++
        "specification lemmas. Nothing unconditional is claimed: every " ++
        "residual is itemized in the per-item cards."
    dependsOn :=
      [ "IUT-I.definition-3.1-D4-supply",
        "IUT-I.definition-3.1-D5-supply",
        "IUT-I.definition-3.1-D6-supply",
        "IUT-I.definition-3.1-D7-supply",
        "IUT-I.definition-3.1-D7a-place-section",
        "IUT-I.definition-3.1-D7b-local-group",
        "IUT-I.definition-3.1-D8-supply",
        "IUT-I.definition-3.1-D9-supply" ] }

/-- The D9 slot wiring: four slots instantiated by the concrete
arithmetic statements, the orbicurve slot kept as a supply. -/
def sourceDefinition31D9ArithmeticSlotWiring : Obligation :=
  { id := "IUT-I.definition-3.1-D9-arithmetic-slot-wiring"
    source :=
      "IUT I, Definition 3.1(a)-(f); consumer side of the " ++
        "`estimates-rec8` integration request"
    status := VerificationStatus.conditional
    note :=
      "The five D9 slots are wired to concrete content on the consumer " ++
        "side: `D9CompatibilitySupply.ofArithmeticSlots` instantiates " ++
        "reduction := `ArithmeticReductionCompatibility` (proved from the " ++
        "reduction and q-parameter cards via " ++
        "`arithmeticReductionCompatibility_of_supply`), torsion := " ++
        "`ArithmeticTorsionCompatibility` (clause projection), sections := " ++
        "`ArithmeticSectionCompatibility` (canonical, unconditional), and " ++
        "cusp := `ArithmeticCuspOriginCompatibility` (from a supplied " ++
        "`TorsionQuotientBoundaryOrigin`); the orbicurve slot remains an " ++
        "explicit source supply with the parked card " ++
        "`IUT-I.definition-3.1-D9-orbicurve-slot`. No slot content is " ++
        "weakened and no gate (D9CompatibilityConstruction / " ++
        "D10InitialThetaConstruction) is closed."
    dependsOn :=
      [ "IUT-I.definition-3.1-D9-supply",
        "IUT-I.definition-3.1-D9-orbicurve-slot" ] }

end Audit

end

end LeanFormal.IUT

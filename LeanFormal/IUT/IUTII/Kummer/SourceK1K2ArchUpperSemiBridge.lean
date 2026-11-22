import LeanFormal.IUT.IUTII.Kummer.K1K2BoundaryReduction
import LeanFormal.IUT.IUTII.Kummer.MonoAnalyticLogShellArchPsiCnsCalibration

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# The archimedean upper-semi bridge between the two frozen records (shape layer)

The II-side record `ArchimedeanLogKummerUpperSemi`
(`VerticalLogKummerOrderedLayer.lean`) has an `archimedean_surjection` field
rendering the archimedean half of [IUTchIII, Proposition 3.5, (ii), (b)]:
for every level `m : ℤ` and iterate length `m' ≥ 1`, the radius-`pi` ball
contains a subset `S` that links onto the unit part on which the iterate is
defined.  The file `MonoAnalyticLogShellArchPsiCnsCalibration.lean` supplies
a calibration inhabitant of that record.

The III-side frozen record `K1VerticalBoundary`
(`IUTIII/Theorem311/SourceK1K2Construction.lean`) has an
`archimedean_surjection` field of a different shape: for every set
`S : Set Real` and every target point `z` of the `m`-step image
(`m : Nat`), there is a source point `y ∈ S` with `z ≤ y`.

This file states the precise shape-level relation between the two fields,
without claiming a record equivalence or any source-level supply.

## Results

* `ArchimedeanLevelSurjectionShape`: the II-side field as a predicate on its
  data.  `archimedeanLevelSurjectionShape_of_record` recovers it from any
  record; `archimedeanLevelSurjectionShape_signCalibration` is the
  calibration instance; `signCalibration_surjectionWitness` unpacks the
  calibration field with the explicit two-point witness set `archSegment`;
  `not_archimedeanLevelSurjectionShape_linkFree` refutes the shape on free
  data, so it is not a tautology.
* `ArchimedeanTargetToSourceLift`: the III-side field as a predicate on an
  image map.  It holds for the empty image (vacuous reading) and for the
  pointwise down closure, and it is refuted by the constant-universe image.
  The shape is a genuine constraint on the image map, but it carries no
  unit-surjection content by itself.
* Every inhabitant of the frozen III records projects to this predicate on
  its own image map (`k1VerticalBoundary_archimedeanTargetToSourceLift`,
  `sourceVertical_archimedeanTargetToSourceLift`).
* `canonicalArchimedeanImage_targetToSource_iff`: at the canonical extension
  `archimedeanImageOfPacket` of the K1/K2 boundary reduction, the III-side
  shape is *equivalent* to the image card `archimedeanTargetLift` (card A1),
  given the well-definedness card N2.  Consequently any inhabitant of the
  frozen `K1VerticalBoundary` yields the canonical shape
  (`k1VerticalBoundary_canonicalArchimedeanLift`).

## Boundary notes (mandatory)

* The calibration inhabitant is a shape pattern, not the arithmetic object
  Psi-cns of the source: its carrier is `ℂ`, its units are `ZMod 2` with the
  sign factor, and its log iterates are `True`.  Nothing here asserts the
  source identification; the calibration pattern is not the Psi-cns object
  itself.
* This bridge is not a record equivalence and asserts no source-level
  supply.  No implication between the two frozen surjection fields is
  proved or claimed: they live over different carriers (`ℂ` versus `Real`)
  and different quantifier shapes (subset surjection onto the defined units
  versus pointwise `≤`-lift through an image map), and the lemmas above
  delimit exactly what each shape does and does not carry.
* The missing link is a dictionary (level reading `Nat → ℤ`, unit reading,
  radius-`pi` ball versus possible-image identification, and the `≤`-link
  reading); supplying it is precisely the source obligation around
  `IUT-II.vertical-log-kummer` / `IUT-III.K1.vertical-log-kummer-boundary`.

Original: IUT III, Proposition 3.5, (ii), (b); Theorem 3.11, (ii), (Ind3)
("certain natural surjections at vQ in Varc_Q"); cf. the (Ind3) discussion
in section 1 of IUT III.

Consumers: the archimedean half of (Ind3) and the R8 side of the K1/K2
boundary reduction.
-/

namespace LeanFormal.IUT

universe u v

namespace SourceK1K2ArchUpperSemiBridge

open MonoAnalyticLogShellArchPsiCnsCalibration
open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open K1K2BoundaryReduction

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. The two field shapes -/

/-- The III-side `archimedean_surjection` field of `K1VerticalBoundary`, read
as a predicate on an image map: every target point of the `m`-step image of
`S` is bounded above by a point of `S`.  This is the shape of card A1 on the
frozen record; it is a reduced form of the surjection direction of
[IUTchIII, Proposition 3.5, (ii), (b)]. -/
def ArchimedeanTargetToSourceLift (image : Nat → Set Real → Set Real) : Prop :=
  ∀ (m : Nat) (z : Real) (S : Set Real), z ∈ image m S → ∃ y, y ∈ S ∧ z ≤ y

/-- The II-side `archimedean_surjection` field of
`ArchimedeanLogKummerUpperSemi`, read as a predicate on the record data: for
each level `m : ℤ` and iterate length `m' ≥ 1`, a subset of the radius-`pi`
ball links onto every defined unit at level `m - m'`. -/
def ArchimedeanLevelSurjectionShape (Unit : ℤ → Type u) (coricModule : Type u)
    (piBall : Set coricModule)
    (link : ∀ (m : ℤ) {m' : ℤ}, coricModule → Unit m' → Prop)
    (defined : ∀ {m : ℤ}, Unit m → Prop) : Prop :=
  ∀ (m : ℤ) {m' : ℤ}, 1 ≤ m' →
    ∃ S : Set coricModule, S ⊆ piBall ∧
      ∀ u : Unit (m - m'), defined u → ∃ s, s ∈ S ∧ link m s u

/-! ## 2. The II side: record, calibration, explicit witness, refutation -/

theorem archimedeanLevelSurjectionShape_of_record
    (A : ArchimedeanLogKummerUpperSemi) :
    ArchimedeanLevelSurjectionShape A.Unit A.coricModule A.piBallImage
      A.coricKummerLink A.iteratedDefined :=
  A.archimedean_surjection

theorem archimedeanLevelSurjectionShape_signCalibration :
    ArchimedeanLevelSurjectionShape
      archimedeanLogKummerUpperSemiSignCalibration.Unit
      archimedeanLogKummerUpperSemiSignCalibration.coricModule
      archimedeanLogKummerUpperSemiSignCalibration.piBallImage
      archimedeanLogKummerUpperSemiSignCalibration.coricKummerLink
      archimedeanLogKummerUpperSemiSignCalibration.iteratedDefined :=
  archimedeanLogKummerUpperSemiSignCalibration.archimedean_surjection

/-- Explicit unpacking of the calibration's surjection field: the witness set
can be taken to be `archSegment` itself, and every unit (an element of
`ZMod 2`) is hit by its sign factor. -/
theorem signCalibration_surjectionWitness (m : ℤ) {m' : ℤ} (hm' : 1 ≤ m') :
    ∃ S : Set ℂ, S = archSegment ∧
      S ⊆ archimedeanLogKummerUpperSemiSignCalibration.piBallImage ∧
      ∀ u : ZMod 2, ∃ s, s ∈ S ∧ s = signFactor u :=
  ⟨archSegment, rfl, fun _ h => h,
    fun u => ⟨signFactor u, signFactor_mem_archSegment u, rfl⟩⟩

/-- Non-vacuity of the calibration witness: both signs of the two-point unit
group are present in `archSegment` as distinct points. -/
theorem archSegment_contains_two_signs :
    (1 : ℂ) ∈ archSegment ∧ (-1 : ℂ) ∈ archSegment ∧ (1 : ℂ) ≠ (-1 : ℂ) :=
  ⟨signFactor_zero.symm ▸ signFactor_mem_archSegment 0,
    signFactor_one.symm ▸ signFactor_mem_archSegment 1, by norm_num⟩

/-- The II-side shape is refutable on free data: with a trivial module, a
link that never holds, and all units defined, no witness set can exist.
Hence the shape is not a tautology. -/
theorem not_archimedeanLevelSurjectionShape_linkFree :
    ¬ ArchimedeanLevelSurjectionShape (fun _ : ℤ => PUnit) PUnit Set.univ
      (fun _ {m'} _ _ => False) (fun {m : ℤ} _ => True) := by
  intro h
  unfold ArchimedeanLevelSurjectionShape at h
  obtain ⟨S, -, hS⟩ := h 0 (m' := 1) (by norm_num : (1 : ℤ) ≤ 1)
  obtain ⟨s, -, hfalse⟩ := hS PUnit.unit trivial
  exact hfalse

/-! ## 3. The III side: shape readings and projection from the records -/

theorem archimedeanTargetToSourceLift_empty :
    ArchimedeanTargetToSourceLift (fun _ _ => (∅ : Set Real)) :=
  fun _ _ _ hz => False.elim hz

theorem archimedeanTargetToSourceLift_downClosure :
    ArchimedeanTargetToSourceLift
      (fun _ S => {z : Real | ∃ y, y ∈ S ∧ z ≤ y}) :=
  fun _ _ _ hz => hz

theorem not_archimedeanTargetToSourceLift_univ :
    ¬ ArchimedeanTargetToSourceLift (fun _ _ => (Set.univ : Set Real)) := by
  intro h
  obtain ⟨y, hy, -⟩ := h 0 0 (∅ : Set Real) (Set.mem_univ 0)
  exact hy

theorem k1VerticalBoundary_archimedeanTargetToSourceLift
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (K : K1VerticalBoundary P Q) :
    ArchimedeanTargetToSourceLift K.archimedeanImage :=
  K.archimedean_surjection

theorem sourceVertical_archimedeanTargetToSourceLift
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (V : SourceVerticalRealization P Q) :
    ArchimedeanTargetToSourceLift V.archimedeanImage :=
  V.archimedean_surjection

/-! ## 4. Canonical reading: the III-side shape is card A1 -/

/-- At the canonical extension `archimedeanImageOfPacket` of the K1/K2
boundary reduction, the III-side shape is equivalent to the image card
`archimedeanTargetLift` (card A1), given the well-definedness card N2.  The
backward direction is `archimedeanImageOfPacket_surjection`; the forward
direction rewrites the packet profile through N2. -/
theorem canonicalArchimedeanImage_targetToSource_iff
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hWD : ind3ImageWellDefined P Q) :
    ArchimedeanTargetToSourceLift (archimedeanImageOfPacket P Q) ↔
      archimedeanTargetLift P Q := by
  constructor
  · intro hshape m c z hz
    have hmem : z ∈ archimedeanImageOfPacket P Q m (Q.possibleImage c) := by
      rw [archimedeanImageOfPacket_profile P Q hWD m c]
      exact hz
    exact hshape m z (Q.possibleImage c) hmem
  · intro hLift m z S hz
    exact archimedeanImageOfPacket_surjection P Q hLift m z S hz

/-- Any inhabitant of the frozen `K1VerticalBoundary` yields the canonical
shape: necessity of the cards N2 and A1 (`k1Boundary_possibleImage_congr`,
`k1Boundary_possibleImage_lift`) composed with the canonical equivalence. -/
theorem k1VerticalBoundary_canonicalArchimedeanLift
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (K : K1VerticalBoundary P Q) :
    ArchimedeanTargetToSourceLift (archimedeanImageOfPacket P Q) :=
  (canonicalArchimedeanImage_targetToSource_iff P Q
      (k1Boundary_possibleImage_congr P Q K)).mpr
    (k1Boundary_possibleImage_lift P Q K)

end SourceK1K2ArchUpperSemiBridge

end LeanFormal.IUT

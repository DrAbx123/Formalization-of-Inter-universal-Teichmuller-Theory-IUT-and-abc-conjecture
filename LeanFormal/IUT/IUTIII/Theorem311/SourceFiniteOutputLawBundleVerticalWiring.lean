import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Realization
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
# K1/K2 realization wiring: five-element reduction of the source input

Task (2026-10-16): reduce the residual card `theorem311SourceInputResidual`
(`SourceFiniteOutputLawBundle.lean`, id
`IUT-III.theorem-3.11-output.source-input-residual`) with the accepted K1/K2
realization (`SourceK1K2Realization.lean`).

The residual card names the accepted route `SourceTheorem311Realization`
(`SourceHodgeTheaterBridge.lean:910`) with five element fields
(`procession`, `packet`, `vertical`, `evaluation`, `genericFamily`) plus a
positive `labelledCount`.  Updated status, evidenced below:

* `procession`, `packet`: still open source data.  No tree declaration
  constructs either outside the completion context, and the K1/K2 realization
  takes them as input (`K1K2Realization.LogShellRayPresentation Q L h`
  characterizes `Q`; it does not construct it).
* `vertical`: conditional construction.  `sourceVerticalRealizationOfImageCards`
  assembles it from `(P, Q)` and the three packet-consistency cards
  (`K1K2BoundaryReduction.nonarchimedeanImageInclusion`,
  `.ind3ImageWellDefined`, `.archimedeanTargetLift`) through the frozen
  card-route `K1K2BoundaryReduction.k1FromImageCards` and the frozen
  `K1VerticalBoundary.toSource` (`SourceK1K2Construction.lean:88`).  The
  accepted realization supplies the other half: its lemmas derive the three
  cards from the log-shell ray presentation plus the four ray laws.  The
  composition is `sourceVerticalRealizationOfRayPresentation` /
  `sourceTheorem311RealizationOfRayPresentation`.  Turing's item-27 wiring
  file (`SourceK1K2VerticalRealization.lean`) is in flight and is deliberately
  not imported; this file uses only the frozen pieces.
* `evaluation`, `genericFamily` (+ `labelledCount`): constructible canonical
  data, `sourceEvaluationBridgeOfVertical` and `identityTheaterFamily`.

Consequence: `Theorem311Source.Input` is constructed from `(P, Q)` plus the
three cards (`sourceInputOfImageCards`; ray-presentation variant
`sourceInputOfRayPresentation`).  The residual gap is exactly the procession
`P`, the packet `Q`, and the three packet-consistency cards; the vertical
log-shell/Kummer identification is no longer part of the gap, because the
accepted K1/K2 realization now supplies it in the shape
`ray presentation -> cards -> boundary -> realization`.

Reduced-form labels: everything below is the frozen interface of
`Theorem311Source.Input`.  Nothing here claims the general Theorem 3.11
statement, and no field is manufactured from `OriginalInput`.

Corpus anchors: IUT III, Theorem 3.11 opening (III:9151-9163), (i) procession
of D-prime-strips (III:9164-9175), (ii) log-volume/Ind3 directions
(III:9176-9191).

Audit records at the end update the residual card; the superseded card text
is preserved in `SourceFiniteOutputLawBundle.lean` with a revision marker.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v w

/-! Wiring namespace: constructions and the exact five-element reduction for
the output-side residual card.  Kept separate from `K1K2Realization` (the
realization-side namespace) and from `SourceFiniteTheorem311` (the finite
carrier namespace). -/
namespace SourceOutputWiring

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. Canonical data for the evaluation, horizontal and family slots -/

/-- Identity evaluation system on a single index type: the frozen record's
laws hold by `rfl`, and no law of the record relates the evaluation data to
`(P, Q, V)`. -/
def identityEvaluationSystem (A : Type u) : EvaluationSystem A A where
  localMap := id
  globalMap := id
  localEqGlobal := fun _ => rfl
  localComp := id
  globalComp := id
  localNaturality := fun _ => rfl
  globalNaturality := fun _ => rfl

/-- Identity horizontal LGP link on a single index type: commuting square
with constant zero labels. -/
def identityHorizontalLGPLink (A : Type u) : HorizontalLGPLink A A where
  left := id
  right := id
  upper := id
  lower := id
  square := fun _ => rfl
  upper_label := fun _ => 0
  lower_label := fun _ => 0
  labels_agree := fun _ => rfl

/-- The canonical distinct-theater family on a single index type: identity
theater map (injective), trivial link, trivial permutation. -/
def identityTheaterFamily (I : Type u) : TheaterFamily I I where
  theater := id
  distinct := fun _ _ h => h
  link := fun _ _ t => t
  link_refl := fun _ _ => rfl
  link_trans := fun _ _ _ _ => rfl
  permutation := Equiv.refl I
  permutation_naturality := fun _ _ => rfl

/-- The evaluation bridge slot of the five-element tuple, filled with the
identity data: all law fields hold definitionally, and the frozen record
imposes no relation between the evaluation/horizontal data and `(P, Q, V)`. -/
def sourceEvaluationBridgeOfVertical
    (P : SourceLGPProcession.{u, v} l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (V : SourceVerticalRealization.{u, v, w} P Q) :
    SourceEvaluationBridge.{u, v, w} P Q V where
  evaluation := identityEvaluationSystem Choice
  horizontal := identityHorizontalLGPLink Choice
  kummer_horizontal := fun _ => rfl
  label_horizontal := fun _ => rfl
  evaluation_horizontal := fun _ => rfl
  upper_horizontal := fun _ => rfl
  horizontal_left_index := fun _ => rfl
  horizontal_lower_index := fun _ => rfl

/-! ## 2. Vertical slot: card route to the frozen realization -/

/-- Vertical element of the five-element tuple from the three
packet-consistency cards, through the frozen card route: assemble
`K1VerticalBoundary` from the cards (`k1FromImageCards`, with the identity
labelled Kummer slot, the only content of the kummer fields at this
interface) and read its `toSource` projection. -/
def sourceVerticalRealizationOfImageCards
    (P : SourceLGPProcession.{u, v} l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (hInc : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (hWD : K1K2BoundaryReduction.ind3ImageWellDefined P Q)
    (hLift : K1K2BoundaryReduction.archimedeanTargetLift P Q) :
    SourceVerticalRealization.{u, v, w} P Q :=
  (K1K2BoundaryReduction.k1FromImageCards P Q hInc hWD hLift
    (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice)).toSource

/-- Exact characterization of the vertical gate at the `(P, Q)` level:
`SourceVerticalRealization` is inhabited if and only if the three
packet-consistency cards hold.  Forward direction: every inhabitant forces
the cards (`sourceVertical_possibleImage_subset/congr/lift`).  Backward
direction: the card route above. -/
theorem sourceVerticalRealization_nonempty_iff_imageCards
    (P : SourceLGPProcession.{u, v} l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P) :
    Nonempty (SourceVerticalRealization.{u, v, w} P Q) ↔
      (K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q ∧
        K1K2BoundaryReduction.ind3ImageWellDefined P Q ∧
        K1K2BoundaryReduction.archimedeanTargetLift P Q) := by
  constructor
  · rintro ⟨V⟩
    exact ⟨K1K2BoundaryReduction.sourceVertical_possibleImage_subset P Q V,
      K1K2BoundaryReduction.sourceVertical_possibleImage_congr P Q V,
      K1K2BoundaryReduction.sourceVertical_possibleImage_lift P Q V⟩
  · rintro ⟨hInc, hWD, hLift⟩
    exact ⟨sourceVerticalRealizationOfImageCards P Q hInc hWD hLift⟩

/-- Vertical element via the accepted K1/K2 realization ray route: derive the
three cards from the log-shell ray presentation and the four ray laws
(`K1K2Realization` E1 lemmas), assemble the boundary
(`k1BoundaryOfLogShellPresentation`) and read its `toSource` projection. -/
def sourceVerticalRealizationOfRayPresentation
    (P : SourceLGPProcession.{u, v} l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : K1K2Realization.LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c')) :
    SourceVerticalRealization.{u, v, w} P Q :=
  (K1K2Realization.k1BoundaryOfLogShellPresentation P Q L h hpres hind3
    hunbounded hsep hclass
    (fun _ => K1K2BoundaryReduction.identityLabelledKummerIso Choice)).toSource

/-! ## 3. The five-element realization and the source-input package -/

/-- The five-element realization assembled from `(P, Q)` and the three cards:
vertical by the card route; evaluation bridge by the canonical identity data;
family by the canonical identity theater family; labelled count one. -/
def sourceTheorem311RealizationOfImageCards
    (P : SourceLGPProcession.{u, v} l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (hInc : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (hWD : K1K2BoundaryReduction.ind3ImageWellDefined P Q)
    (hLift : K1K2BoundaryReduction.archimedeanTargetLift P Q) :
    SourceTheorem311Realization.{u, v, w} l Label Choice where
  procession := P
  packet := Q
  vertical := sourceVerticalRealizationOfImageCards P Q hInc hWD hLift
  evaluation := sourceEvaluationBridgeOfVertical P Q
    (sourceVerticalRealizationOfImageCards P Q hInc hWD hLift)
  genericFamily := identityTheaterFamily Choice
  labelledCount := 1
  labelledCount_pos := Nat.one_pos

/-- The source-input package of the residual card, constructed from
`(P, Q)` and the three packet-consistency cards. -/
def sourceInputOfImageCards
    (P : SourceLGPProcession.{u, v} l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (hInc : K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q)
    (hWD : K1K2BoundaryReduction.ind3ImageWellDefined P Q)
    (hLift : K1K2BoundaryReduction.archimedeanTargetLift P Q) :
    Theorem311Source.Input.{u, v, w} Label Choice :=
  (sourceTheorem311RealizationOfImageCards P Q hInc hWD hLift).input

/-- The five-element realization via the accepted K1/K2 ray-presentation
route: vertical from `sourceVerticalRealizationOfRayPresentation`, the
remaining slots canonical as above. -/
def sourceTheorem311RealizationOfRayPresentation
    (P : SourceLGPProcession.{u, v} l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : K1K2Realization.LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c')) :
    SourceTheorem311Realization.{u, v, w} l Label Choice where
  procession := P
  packet := Q
  vertical := sourceVerticalRealizationOfRayPresentation P Q L h hpres hind3
    hunbounded hsep hclass
  evaluation := sourceEvaluationBridgeOfVertical P Q
    (sourceVerticalRealizationOfRayPresentation P Q L h hpres hind3
      hunbounded hsep hclass)
  genericFamily := identityTheaterFamily Choice
  labelledCount := 1
  labelledCount_pos := Nat.one_pos

/-- The source-input package via the ray-presentation route. -/
def sourceInputOfRayPresentation
    (P : SourceLGPProcession.{u, v} l Label Choice)
    (Q : SourcePacketRealization.{u, v, w} P)
    (L : Set Real) (h : Choice → Real)
    (hpres : K1K2Realization.LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c')) :
    Theorem311Source.Input.{u, v, w} Label Choice :=
  (sourceTheorem311RealizationOfRayPresentation P Q L h hpres hind3 hunbounded
    hsep hclass).input

end SourceOutputWiring

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Wiring record for the vertical element of the output-side residual card:
the gate `Nonempty (SourceVerticalRealization P Q)` is exactly the three
packet-consistency cards, and the accepted K1/K2 realization derives those
cards from the log-shell ray presentation. -/
def sourceOutputWiringK1K2 : Obligation :=
  { id := "IUT-III.concrete-source-output-law-bundle.vertical-wiring"
    source := "IUT III, Theorem 3.11, (ii) (Ind3 directions); Proposition 3.5"
    status := VerificationStatus.interface
    note :=
      "Vertical wiring of the output-side residual card. Card route: " ++
        "`sourceVerticalRealizationOfImageCards` constructs " ++
        "`SourceVerticalRealization` from (P, Q) plus the three cards " ++
        "(nonarchimedeanImageInclusion, ind3ImageWellDefined, " ++
        "archimedeanTargetLift) via the frozen `k1FromImageCards` and " ++
        "`toSource`; `sourceVerticalRealization_nonempty_iff_imageCards` is " ++
        "the exact characterization. Ray route: the accepted K1/K2 " ++
        "realization derives the three cards from the log-shell ray " ++
        "presentation plus hind3/hunbounded/hsep/hclass; " ++
        "`sourceTheorem311RealizationOfRayPresentation` composes it with the " ++
        "canonical evaluation and family data. Evaluation, family and " ++
        "labelled count are canonical identity data; no field is " ++
        "manufactured from OriginalInput. Reduced form: this is not the " ++
        "original Proposition 3.5 statement; the three cards remain " ++
        "source-facing."
    dependsOn :=
      [ "IUT-III.K1.vertical-log-kummer-boundary",
        "IUT-II.vertical-log-kummer",
        "IUT-III.concrete-source-output-law-bundle" ] }

/-- Five-element reduction of `theorem311SourceInputResidual`
(`SourceFiniteOutputLawBundle.lean`): procession and packet remain open
source data; vertical is a conditional construction; evaluation and family
are canonical.  The source-input package is constructed from `(P, Q)` plus
the three packet-consistency cards. -/
def theorem311SourceInputResidualReduction : Obligation :=
  { id := "IUT-III.theorem-3.11-output.source-input-residual.reduction"
    source := "IUT III, Theorem 3.11, opening (III:9151-9163), (i) (III:9164-9175), (ii) (III:9176-9191)"
    status := VerificationStatus.interface
    note :=
      "Five-element reduction of the source-input residual. Status table: " ++
        "(1) procession: still open - no construction of SourceLGPProcession " ++
        "outside the completion context; (2) packet: still open - the ray " ++
        "presentation characterizes Q, it does not construct it; " ++
        "(3) vertical: conditional construction - either from (P, Q) plus " ++
        "the three cards, or via the accepted K1/K2 realization ray route; " ++
        "(4) evaluation: constructible - sourceEvaluationBridgeOfVertical; " ++
        "(5) genericFamily with labelledCount: constructible - " ++
        "identityTheaterFamily, count one. Consequence: Theorem311Source.Input " ++
        "is constructed from (P, Q) plus the three cards " ++
        "(`sourceInputOfImageCards`, `sourceInputOfRayPresentation`); the " ++
        "residual is exactly the procession, the packet, and the three " ++
        "packet-consistency cards. This is the frozen input interface, not " ++
        "the general Theorem 3.11 statement."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output.source-input-residual",
        "IUT-III.concrete-source-output-law-bundle.vertical-wiring" ] }

end LeanFormal.IUT.Audit

import LeanFormal.IUT.IUTIII.Theorem311.HullImageDirectednessStatementLayer
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Realization
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2CardReduction

/-!
# hpres adoption package: attained hull cuts for the `SourceK1K2` consumer chain

Run `k1k2-adoption-20261017`.  New file; no existing source file is modified.

This file adopts the hull-presentation vocabulary frozen in
`HullImageDirectednessStatementLayer.lean` into the `SourceK1K2*` consumer chain.

* `PossibleImageDirected`, `PossibleImageUpClosedIn` and
  `familyRayCutIn_iff_of_subset` are re-exported as aliases; no proof is copied.
* `AttainedHullCut` is the exact witness type of the attainment slot: a height
  function that is a lower bound of every possible image and whose `L`-principal
  filter is contained in that image.
* `logShellRayPresentation_iff_directed_upClosedIn_attained` is the
  attainment-slot criterion: for a fixed height `h`, the ray presentation holds
  iff the possible-image family is directed, up-closed in `L`, and `h` attains
  the cut.
* `logShellRayPresentation_of_directed_upClosedIn_attained` is the adoption form
  required by the handoff.  `possibleImageDirected_upClosedIn_of_attainedHullCut`
  records that directedness and up-closure are consequences of an attainment
  witness, so the adoption form adds no strength beyond the witness.
* `k1BoundaryOfAttainedHullCut` wires the witness into the frozen consumer
  `k1BoundaryOfLogShellPresentation` (`SourceK1K2Realization.lean:159`); the
  resulting `K1VerticalBoundary` is consumed through `toSource`
  (`SourceK1K2Construction.lean:88`) at item 27
  (`SourceK1K2VerticalRealization.lean:71`).
* `HullCutAttainmentGap` is the precise carrier-level gap card.  Given
  containment of the possible images in `L`, it is equivalent to the existence
  of a ray presentation, so it is not a weaker input that could replace hpres.

Three-state: every declaration below is proved.  No inhabitant of
`HullCutAttainmentGap` for the actual IUT packet is provided; the equivalence
below identifies that missing inhabitant with the open hpres problem.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanFormal.IUT

universe u v

namespace K1K2Realization

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

noncomputable section

namespace HullPresentationAdoption

/-! ## 1. Re-exported vocabulary -/

/-- Re-export of `PossibleImageDirected` (frozen in
`HullImageDirectednessStatementLayer.lean`) as the adopted directedness slot. -/
abbrev PossibleImageDirected {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) : Prop :=
  _root_.LeanFormal.IUT.K1K2Realization.PossibleImageDirected Q

/-- Re-export of `PossibleImageUpClosedIn` as the adopted up-closure slot. -/
abbrev PossibleImageUpClosedIn {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (L : Set Real) : Prop :=
  _root_.LeanFormal.IUT.K1K2Realization.PossibleImageUpClosedIn Q L

/-- Re-export of the frozen criterion `familyRayCutIn_iff_of_subset`: with
containment fixed, the ray-cut presentation is exactly the attainment slot. -/
theorem familyRayCutIn_iff_of_subset {σ : Type*} {L : Set Real} {S : σ → Set Real}
    (hsub : ∀ c, S c ⊆ L) :
    FamilyRayCutIn L S ↔ FamilyCutAttainedIn L S :=
  _root_.LeanFormal.IUT.K1K2Realization.familyRayCutIn_iff_of_subset hsub

/-! ## 2. The attainment witness and the criterion -/

/-- The exact witness type of the attainment slot.  `height` is the generator
family; `le_height` makes it a lower bound of every possible image;
`mem_of_le_height` puts every `L`-point above the generator back into the image.
Together with containment `possibleImage c ⊆ L` these two laws state exactly
`possibleImage c = L ∩ Set.Ici (height c)`. -/
structure AttainedHullCut {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (L : Set Real) where
  height : Choice → Real
  le_height : ∀ c, ∀ x : Real, x ∈ Q.possibleImage c → height c ≤ x
  mem_of_le_height : ∀ c, ∀ x : Real, x ∈ L → height c ≤ x →
    x ∈ Q.possibleImage c

/-- The witness type is exactly the frozen attainment predicate. -/
theorem nonempty_attainedHullCut_iff_familyCutAttainedIn
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) :
    Nonempty (AttainedHullCut Q L) ↔ FamilyCutAttainedIn L Q.possibleImage := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.height, W.le_height, W.mem_of_le_height⟩
  · rintro ⟨m, hlow, hcof⟩
    exact ⟨⟨m, hlow, hcof⟩⟩

/-- **Attainment-slot criterion.**  Fix a height `h` and assume the possible
images are contained in `L`.  Then `h` presents every possible image as the
`L`-trace of a closed upper ray iff the family is directed, every image is
up-closed in `L`, and `h` is an attained generator of the cut. -/
theorem logShellRayPresentation_iff_directed_upClosedIn_attained
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hsub : ∀ c, Q.possibleImage c ⊆ L) :
    LogShellRayPresentation Q L h ↔
      PossibleImageDirected Q ∧ PossibleImageUpClosedIn Q L ∧
        (∀ c, ∀ x : Real, x ∈ Q.possibleImage c → h c ≤ x) ∧
        (∀ c, ∀ x : Real, x ∈ L → h c ≤ x → x ∈ Q.possibleImage c) := by
  constructor
  · intro hpres
    exact ⟨possibleImageDirected_of_logShellRayPresentation Q L h hpres,
      possibleImageUpClosedIn_of_logShellRayPresentation Q L h hpres,
      fun c x hx => by
        rw [hpres c] at hx
        exact hx.2,
      fun c x hxL hhx => by
        rw [hpres c]
        exact ⟨hxL, hhx⟩⟩
  · rintro ⟨-, -, hlow, hcof⟩ c
    ext x
    constructor
    · intro hx
      exact ⟨hsub c hx, hlow c x hx⟩
    · intro hx
      exact hcof c x hx.1 hx.2

/-- Minimal sufficient form: containment plus an attainment witness give the ray
presentation, with the witness height as the presenting height. -/
theorem logShellRayPresentation_of_attainedHullCut
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (hsub : ∀ c, Q.possibleImage c ⊆ L)
    (W : AttainedHullCut Q L) :
    LogShellRayPresentation Q L W.height := by
  intro c
  ext x
  constructor
  · intro hx
    exact ⟨hsub c hx, W.le_height c x hx⟩
  · intro hx
    exact W.mem_of_le_height c x hx.1 hx.2

/-- Directedness and up-closure are consequences of an attainment witness (given
containment), not extra hypotheses of the adoption package. -/
theorem possibleImageDirected_upClosedIn_of_attainedHullCut
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (hsub : ∀ c, Q.possibleImage c ⊆ L)
    (W : AttainedHullCut Q L) :
    PossibleImageDirected Q ∧ PossibleImageUpClosedIn Q L := by
  have hpres := logShellRayPresentation_of_attainedHullCut Q L hsub W
  exact ⟨possibleImageDirected_of_logShellRayPresentation Q L W.height hpres,
    possibleImageUpClosedIn_of_logShellRayPresentation Q L W.height hpres⟩

/-- **Adoption form.**  Directedness, up-closure and a concrete attainment
witness give the log-shell ray presentation.  The first two conjuncts are the
adopted vocabulary; the previous theorem shows they already follow from the
witness, so this form adds no strength beyond the attainment slot. -/
theorem logShellRayPresentation_of_directed_upClosedIn_attained
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (hdir : PossibleImageDirected Q)
    (hup : PossibleImageUpClosedIn Q L)
    (hsub : ∀ c, Q.possibleImage c ⊆ L) (W : AttainedHullCut Q L) :
    LogShellRayPresentation Q L W.height :=
  (logShellRayPresentation_iff_directed_upClosedIn_attained Q L W.height hsub).mpr
    ⟨hdir, hup, W.le_height, W.mem_of_le_height⟩

/-! ## 3. Consumer wiring into the `SourceK1K2` chain -/

/-- Consumer wiring: an attained hull cut, the containment law, the four frozen
card hypotheses and a labelled Kummer slot produce the `K1VerticalBoundary`
through the frozen consumer `k1BoundaryOfLogShellPresentation`. -/
def k1BoundaryOfAttainedHullCut
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (L : Set Real) (W : AttainedHullCut Q L)
    (hsub : ∀ c, Q.possibleImage c ⊆ L)
    (hind3 : ∀ (m : Nat) (c : Choice), W.height (P.ind3 m c) ≤ W.height c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), W.height c = W.height c' →
      W.height (P.ind3 m c) = W.height (P.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice) :
    K1VerticalBoundary P Q :=
  k1BoundaryOfLogShellPresentation P Q L W.height
    (logShellRayPresentation_of_attainedHullCut Q L hsub W)
    hind3 hunbounded hsep hclass κ

/-- The same wiring read at the frozen source record: `toSource` of the assembled
K1 boundary is the item-27 `SourceVerticalRealization`. -/
def sourceVerticalRealizationOfAttainedHullCut
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (L : Set Real) (W : AttainedHullCut Q L)
    (hsub : ∀ c, Q.possibleImage c ⊆ L)
    (hind3 : ∀ (m : Nat) (c : Choice), W.height (P.ind3 m c) ≤ W.height c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), W.height c = W.height c' →
      W.height (P.ind3 m c) = W.height (P.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice) :
    SourceVerticalRealization P Q :=
  (k1BoundaryOfAttainedHullCut P Q L W hsub hind3 hunbounded hsep hclass κ).toSource

/-! ## 4. The gap card and the frozen separation -/

/-- The precise carrier-level gap: an attained ray cut for the possible-image
family in `L`.  This is a proposition about a concrete witness, not a field
promised by another record. -/
def HullCutAttainmentGap {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (L : Set Real) : Prop :=
  Nonempty (AttainedHullCut Q L)

/-- Exactness of the gap card: given containment, the gap is equivalent to the
existence of a log-shell ray presentation.  It is therefore not weaker than
hpres and cannot be assumed as a shortcut. -/
theorem hullCutAttainmentGap_iff_exists_logShellRayPresentation
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (hsub : ∀ c, Q.possibleImage c ⊆ L) :
    HullCutAttainmentGap Q L ↔
      ∃ h : Choice → Real, LogShellRayPresentation Q L h := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.height, logShellRayPresentation_of_attainedHullCut Q L hsub W⟩
  · rintro ⟨h, hpres⟩
    refine ⟨⟨h, ?_, ?_⟩⟩
    · intro c x hx
      rw [hpres c] at hx
      exact hx.2
    · intro c x hxL hhx
      rw [hpres c]
      exact ⟨hxL, hhx⟩

/-- The frozen two-singleton separation, read at the attainment slot: under
containment, two singleton images with distinct values force the attainment
slot to fail. -/
theorem not_familyCutAttainedIn_of_two_singletonImages
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (hsub : ∀ c, Q.possibleImage c ⊆ L)
    {c c' : Choice} {v v' : Real} (hvv' : v < v')
    (hc : Q.possibleImage c = {v}) (hc' : Q.possibleImage c' = {v'}) :
    ¬ FamilyCutAttainedIn L Q.possibleImage := by
  intro hatt
  obtain ⟨h, hpres⟩ := (familyRayCutIn_iff_of_subset hsub).mpr hatt
  exact not_logShellRayPresentation_of_two_singletonImages P Q L h hvv' hc hc' hpres

/-- Gap-card form of the separation: the two-singleton obstruction refutes the
carrier-level attainment gap. -/
theorem not_hullCutAttainmentGap_of_two_singletonImages
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (hsub : ∀ c, Q.possibleImage c ⊆ L)
    {c c' : Choice} {v v' : Real} (hvv' : v < v')
    (hc : Q.possibleImage c = {v}) (hc' : Q.possibleImage c' = {v'}) :
    ¬ HullCutAttainmentGap Q L :=
  fun hgap =>
    not_familyCutAttainedIn_of_two_singletonImages Q L hsub hvv' hc hc'
      ((nonempty_attainedHullCut_iff_familyCutAttainedIn Q L).mp hgap)

end HullPresentationAdoption

end

end K1K2Realization

end LeanFormal.IUT

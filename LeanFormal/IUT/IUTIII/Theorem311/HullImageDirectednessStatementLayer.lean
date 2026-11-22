/-
# possibleImage directedness: statement freeze and the exact gap

Probe file (run `hull-presentation-routes-20261016`, agent Noether), read-only with
respect to every other file.  The `possibleImage` field is declared in
`SourcePacketRealization` (`SourceHodgeTheaterBridge.lean:349`); the ray-presentation
consumer is `LogShellRayPresentation` (`SourceK1K2Realization.lean:107`); the frozen
T4 probe `HullDirectednessCovolumeSignProbe.lean` proved the directedness and
up-closure consequences.  This file freezes the statement layer requested for the
directedness route and records the exact logical status of the three proposed
components (directed / up-closed / generator attained):

* `PossibleImageDirected` / `PossibleImageUpClosedIn`: the named hypotheses at the
  interface shape; both follow from a ray presentation.
* `FamilyDirected` / `FamilyUpClosedIn` / `FamilyCutAttainedIn` / `FamilyRayCutIn`:
  the abstract slots; a presentation implies all three, and `FamilyCutAttainedIn`
  together with containment is equivalent to the presentation
  (`familyRayCutIn_iff_of_subset`), so the characterization reduces to the
  attainment slot.
* Directedness plus up-closure alone are not sufficient: the frozen open-ray family
  is directed and up-closed, yet has no ray-cut presentation for any log-shell set
  `L` (`not_openRayFamily_familyRayCutIn`, strengthening the frozen `L = univ` kill);
  the missing component is attainment
  (`not_familyCutAttainedIn_univ_openRayFamily`).
* Concrete finite model: `(finiteOutput l).possibleImage c = {normalizedLogVolume l c}`
  (from `HullEnvelopeConditionsDischarge.lean`) and `ind3Lift 1` strictly increases
  the value, so the model's possible-image family is not directed
  (`not_familyDirected_finiteOutput`): the directedness route cannot be instantiated
  on that model, closing the carrier-directedness check left open in the T4 report.

Three-state: everything Lean-visible below is proved.  Adoption of this freeze into
the `SourceK1K2*` files is an owner decision and is not made here.
-/

import LeanFormal.IUT.IUTIII.Theorem311.HullDirectednessCovolumeSignProbe
import LeanFormal.IUT.IUTIII.Theorem311.HullEnvelopeConditionsDischarge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanFormal.IUT

universe u v

namespace K1K2Realization

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

noncomputable section

/-! ## 1. The named hypotheses at the interface shape -/

/-- Statement freeze: the possible-image family of the packet `Q` is directed for the
inclusion order. -/
def PossibleImageDirected {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) : Prop :=
  ∀ c c' : Choice, ∃ k : Choice,
    Q.possibleImage c ≤ Q.possibleImage k ∧ Q.possibleImage c' ≤ Q.possibleImage k

/-- The up-closure slot at the interface: every possible image is up-closed inside
the log-shell set `L`. -/
def PossibleImageUpClosedIn {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (L : Set Real) : Prop :=
  ∀ c, ∀ x, x ∈ Q.possibleImage c → ∀ y, y ∈ L → x ≤ y → y ∈ Q.possibleImage c

/-- A ray presentation forces directedness (re-export of the frozen
`logShellRayPresentation_directed` under the frozen predicate name). -/
theorem possibleImageDirected_of_logShellRayPresentation
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h) : PossibleImageDirected Q :=
  fun c c' => logShellRayPresentation_directed Q L h hpres c c'

/-- A ray presentation forces up-closure inside `L` (re-export of the frozen
`logShellRayPresentation_image_upClosedIn`). -/
theorem possibleImageUpClosedIn_of_logShellRayPresentation
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h) : PossibleImageUpClosedIn Q L :=
  fun c => logShellRayPresentation_image_upClosedIn Q L h hpres c

/-! ## 2. The abstract slots and their exact relations -/

section Abstract

variable {σ : Type*}

/-- The directedness slot: any two members have an upper bound inside the family. -/
def FamilyDirected (S : σ → Set Real) : Prop :=
  ∀ c c', ∃ k, S c ⊆ S k ∧ S c' ⊆ S k

/-- The principal-filter-compatibility slot: up-closure inside `L`. -/
def FamilyUpClosedIn (L : Set Real) (S : σ → Set Real) : Prop :=
  ∀ c, ∀ x, x ∈ S c → ∀ y, y ∈ L → x ≤ y → y ∈ S c

/-- The generator-attainment slot: one lower-bound family `m` that is cofinal for
membership in `L`; equivalently each member is the `L`-trace of the closed ray
`[m c, +inf)` with the generator attained as a lower bound of the member. -/
def FamilyCutAttainedIn (L : Set Real) (S : σ → Set Real) : Prop :=
  ∃ m : σ → Real,
    (∀ c, ∀ x ∈ S c, m c ≤ x) ∧ (∀ c, ∀ x, x ∈ L → m c ≤ x → x ∈ S c)

/-- The presentation shape: every member is the `L`-trace of a closed upper ray. -/
def FamilyRayCutIn (L : Set Real) (S : σ → Set Real) : Prop :=
  ∃ h : σ → Real, ∀ c, S c = L ∩ Set.Ici (h c)

/-- With containment of the family in `L` fixed, the ray-cut presentation is exactly
the attainment slot: the generator `m c` is the ray's lower bound. -/
theorem familyRayCutIn_iff_of_subset {L : Set Real} {S : σ → Set Real}
    (hsub : ∀ c, S c ⊆ L) :
    FamilyRayCutIn L S ↔ FamilyCutAttainedIn L S := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, fun c x hx => ?_, fun c x hxL hmx => ?_⟩
    · rw [hh c] at hx
      exact hx.2
    · rw [hh c]
      exact ⟨hxL, hmx⟩
  · rintro ⟨m, hlow, hcof⟩
    refine ⟨m, fun c => ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨hsub c hx, hlow c x hx⟩
    · intro hx
      exact hcof c x hx.1 hx.2

/-- Necessary half: a presentation makes the family directed. -/
theorem familyDirected_of_familyRayCutIn {L : Set Real} {S : σ → Set Real}
    (h : FamilyRayCutIn L S) : FamilyDirected S := by
  obtain ⟨m, hm⟩ := h
  intro c c'
  rcases le_total (m c) (m c') with hle | hle
  · refine ⟨c, subset_rfl, ?_⟩
    intro x hx
    rw [hm c'] at hx
    rw [hm c]
    exact ⟨hx.1, le_trans hle hx.2⟩
  · refine ⟨c', ?_, subset_rfl⟩
    intro x hx
    rw [hm c] at hx
    rw [hm c']
    exact ⟨hx.1, le_trans hle hx.2⟩

/-- Necessary half: a presentation makes every member up-closed inside `L`. -/
theorem familyUpClosedIn_of_familyRayCutIn {L : Set Real} {S : σ → Set Real}
    (h : FamilyRayCutIn L S) : FamilyUpClosedIn L S := by
  obtain ⟨m, hm⟩ := h
  intro c x hx y hyL hxy
  rw [hm c] at hx
  rw [hm c]
  exact ⟨hyL, le_trans hx.2 hxy⟩

/-- Necessary half: a presentation supplies the attainment slot. -/
theorem familyCutAttainedIn_of_familyRayCutIn {L : Set Real} {S : σ → Set Real}
    (h : FamilyRayCutIn L S) : FamilyCutAttainedIn L S := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun c x hx => ?_, fun c x hxL hmx => ?_⟩
  · rw [hm c] at hx
    exact hx.2
  · rw [hm c]
    exact ⟨hxL, hmx⟩

/-- Up-closure in `Set.univ` weakens to up-closure in any `L`. -/
theorem familyUpClosedIn_of_univ {L : Set Real} {S : σ → Set Real}
    (h : FamilyUpClosedIn Set.univ S) : FamilyUpClosedIn L S :=
  fun c x hx y _ hxy => h c x hx y (Set.mem_univ y) hxy

end Abstract

/-! ## 3. The separation: directed plus up-closed is not enough -/

/-- The frozen open-ray family is directed. -/
theorem familyDirected_openRayFamily : FamilyDirected openRayFamily :=
  fun b b' => openRayFamily_directed b b'

/-- The frozen open-ray family is up-closed in `Set.univ`. -/
theorem familyUpClosedIn_univ_openRayFamily :
    FamilyUpClosedIn Set.univ openRayFamily :=
  fun b x hx y _ hxy => openRayFamily_upClosed b x hx y hxy

/-- Stronger kill: the open-ray family has no ray-cut presentation for any log-shell
set `L`, so directedness and up-closure do not force attainment.  This strengthens
the frozen `not_openRayFamily_single_rayCut` (the `L = Set.univ` case). -/
theorem not_openRayFamily_familyRayCutIn (L : Set Real) :
    ¬ FamilyRayCutIn L openRayFamily := by
  rintro ⟨m, hm⟩
  have hzero_mem : (0 : Real) ∈ L := by
    have hz : (0 : Real) ∈ openRayFamily true := by
      norm_num [openRayFamily]
    rw [hm true] at hz
    exact hz.1
  have hIoi_mem : ∀ x : Real, x ∈ Set.Ioi (0 : Real) → x ∈ L := by
    intro x hx
    have hx' : x ∈ openRayFamily false := by
      simpa [openRayFamily] using hx
    rw [hm false] at hx'
    exact hx'.1
  have hm_le : m false ≤ 0 := by
    by_contra hlt
    have hpos : (0 : Real) < m false := not_le.mp hlt
    have hhalf : m false / 2 ∈ Set.Ioi (0 : Real) := by
      simp only [Set.mem_Ioi]
      linarith
    have hhalfL : m false / 2 ∈ L := hIoi_mem (m false / 2) hhalf
    have hhalf' : m false / 2 ∈ openRayFamily false := by
      simpa [openRayFamily] using hhalf
    rw [hm false] at hhalf'
    have hge : m false ≤ m false / 2 := hhalf'.2
    linarith
  have hz : (0 : Real) ∈ openRayFamily false := by
    rw [hm false]
    exact ⟨hzero_mem, hm_le⟩
  simp [openRayFamily] at hz

/-- The missing component, stated as a refutation: the open-ray family fails the
attainment slot for `L = Set.univ` while being directed and up-closed in `Set.univ`. -/
theorem not_familyCutAttainedIn_univ_openRayFamily :
    ¬ FamilyCutAttainedIn Set.univ openRayFamily := by
  intro h
  exact not_openRayFamily_familyRayCutIn Set.univ
    ((familyRayCutIn_iff_of_subset (L := Set.univ) (S := openRayFamily)
      (fun c x _ => Set.mem_univ x)).mpr h)

/-- Spec-freeze separation: directedness plus up-closure are not sufficient for a
ray-cut presentation (missing component: generator attainment). -/
theorem directed_upClosed_not_sufficient_for_rayCut :
    ∃ S : Bool → Set Real, FamilyDirected S ∧ FamilyUpClosedIn Set.univ S ∧
      ∀ L : Set Real, ¬ FamilyRayCutIn L S :=
  ⟨openRayFamily, familyDirected_openRayFamily, familyUpClosedIn_univ_openRayFamily,
    not_openRayFamily_familyRayCutIn⟩

/-! ## 4. The concrete finite model is not directed -/

section ConcreteModelTest

open ConcreteFiniteTheorem311

/-- The possible-image family of the concrete finite model is not directed: all
images are singletons with values strictly increased by `ind3Lift 1`, so the images
at `base` and `ind3Lift 1 base` have no common upper bound inside the family. -/
theorem not_familyDirected_finiteOutput (l : PrimeGeFive) :
    ¬ FamilyDirected (fun c : ProcessionChoice l => (finiteOutput l).possibleImage c) := by
  intro hdir
  obtain ⟨k, h1, h2⟩ :=
    hdir ProcessionChoice.base (ProcessionChoice.ind3Lift 1 ProcessionChoice.base)
  have e1 : normalizedLogVolume l ProcessionChoice.base = normalizedLogVolume l k := by
    have hmem : normalizedLogVolume l ProcessionChoice.base ∈
        (finiteOutput l).possibleImage k :=
      h1 (by
        change normalizedLogVolume l ProcessionChoice.base ∈
          (finiteOutput l).possibleImage ProcessionChoice.base
        rw [finiteOutput_possibleImage_eq_singleton]
        exact Set.mem_singleton _)
    rw [finiteOutput_possibleImage_eq_singleton] at hmem
    exact Set.mem_singleton_iff.mp hmem
  have e2 : normalizedLogVolume l (ProcessionChoice.ind3Lift 1 ProcessionChoice.base) =
      normalizedLogVolume l k := by
    have hmem : normalizedLogVolume l (ProcessionChoice.ind3Lift 1 ProcessionChoice.base) ∈
        (finiteOutput l).possibleImage k :=
      h2 (by
        change normalizedLogVolume l (ProcessionChoice.ind3Lift 1 ProcessionChoice.base) ∈
          (finiteOutput l).possibleImage (ProcessionChoice.ind3Lift 1 ProcessionChoice.base)
        rw [finiteOutput_possibleImage_eq_singleton]
        exact Set.mem_singleton _)
    rw [finiteOutput_possibleImage_eq_singleton] at hmem
    exact Set.mem_singleton_iff.mp hmem
  exact absurd (e1.trans e2.symm)
    (ne_of_lt (finiteOutput_normalizedLogVolume_lt_ind3Lift_one l ProcessionChoice.base))

end ConcreteModelTest

end

end K1K2Realization

end LeanFormal.IUT

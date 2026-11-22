import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2HullPresentationAdoption
import LeanFormal.IUT.Audit.Status

/-!
# Concrete finite models of the attained hull cut (`AttainedHullCut`)

Run `attained-hull-cut-model-20261017`.  New file; no existing source file is
modified.

The adoption package (`SourceK1K2HullPresentationAdoption.lean`) freezes

* the exact witness type `AttainedHullCut Q L` of the attainment slot, and
* the attainment-slot criterion
  `logShellRayPresentation_iff_directed_upClosedIn_attained`: for a fixed height
  `h` and containment `possibleImage c ⊆ L`, the ray presentation
  `Q.possibleImage c = L ∩ Set.Ici (h c)` holds iff the possible-image family is
  directed, up-closed in `L`, and `h` attains the cut;

but provides no inhabitant of the witness type.  This file supplies concrete
*finite models* of the witness type, over an arbitrary frozen packet interface
`P : SourceLGPProcession l Label Choice`, and verifies the three conditions of
the criterion against the frozen theorem itself.

## Models

* `finitePacketModel P` (routes 1/2): the packet realization whose carrier is
  `PUnit`, `logVolume = 0`, `determinant = 1`, and whose possible-image family
  is the *constant* finite set `finiteLogShellSet = {0, 1, 2}`
  (`Set.range (fun n : Fin 3 => (n : Real))`); the log-shell set is
  `L = finiteLogShellSet`.
* `univRayPacketModel P` (route 1): the same realization with the constant
  ray family `Set.Ici 0` and `L = Set.univ`.
* `twoSingletonFamily` (route 3, boundary contrast): the separated-singletons
  family `false ↦ {0}`, `true ↦ {1}`; it is neither directed nor cut-attained,
  so the finite models above are not vacuous.

The height in both models is the constant `0`; every defining law of
`SourcePacketRealization` holds definitionally because the family is constant.

## Faithfulness boundary (explicit)

A model instance is NOT the source-level hpres statement:

* `P` is an arbitrary frozen packet interface, not the actual IUT packet; no
  inhabitant of `SourceDefinition31Data` (the D3-D11 source gate) is
  manufactured here, so the concrete arithmetic procession is not constructed.
* Even for a fixed `P`, the packet realization `finitePacketModel P` is a
  synthetic realization with a constant possible-image family; it is not the
  arithmetic possible-image family of the paper's packet.
* Accordingly, `Nonempty (AttainedHullCut Q L)` is proved only for the
  synthetic `Q` constructed below.  Nothing here asserts the attainment slot
  for the actual IUT packet; the source-level hpres problem remains open.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanFormal.IUT

universe u v w

namespace K1K2Realization

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

noncomputable section

namespace HullPresentationAdoption

/-! ## 1. The finite log-shell set `L = {0, 1, 2}` -/

/-- The finite log-shell set of the finite model: the range of `Fin 3` in `Real`. -/
def finiteLogShellSet : Set Real :=
  Set.range (fun n : Fin 3 => (n : Real))

theorem zero_mem_finiteLogShellSet : (0 : Real) ∈ finiteLogShellSet :=
  ⟨0, by simp⟩

theorem finiteLogShellSet_nonneg {x : Real} (hx : x ∈ finiteLogShellSet) :
    0 ≤ x := by
  rcases hx with ⟨n, rfl⟩
  positivity

/-! ## 2. The finite packet model (routes 1 and 2) -/

/-- The finite packet realization over an arbitrary frozen packet interface:
`PUnit` carriers, trivial arithmetic volume/determinant, and the constant
finite possible-image family `finiteLogShellSet`. -/
noncomputable def finitePacketModel (P : SourceLGPProcession l Label Choice) :
    SourcePacketRealization.{u, v, 0} P where
  carrier := fun _ => PUnit
  distinguished := fun _ => PUnit.unit
  logVolume := fun _ => 0
  determinant := fun _ => 1
  determinant_positive := fun _ => by norm_num
  log_determinant := fun _ => Real.log_one
  possibleImage := fun _ => finiteLogShellSet
  possibleImage_nonempty := fun _ => ⟨0, zero_mem_finiteLogShellSet⟩
  ind1_volume := fun _ _ => rfl
  ind2_volume := fun _ _ => rfl
  ind3_volume := fun _ _ => le_rfl
  ind1_determinant := fun _ _ => rfl
  ind2_determinant := fun _ _ => rfl
  ind3_determinant := fun _ _ => le_rfl
  image_ind1 := fun _ _ => rfl
  image_ind2 := fun _ _ => rfl
  image_ind3 := fun _ _ z hz => ⟨z, hz, le_rfl⟩

@[simp] theorem finitePacketModel_possibleImage
    (P : SourceLGPProcession l Label Choice) (c : Choice) :
    (finitePacketModel P).possibleImage c = finiteLogShellSet := rfl

/-- The attained hull cut of the finite model: constant height `0`. -/
noncomputable def finitePacketAttainedCut
    (P : SourceLGPProcession l Label Choice) :
    AttainedHullCut (finitePacketModel P) finiteLogShellSet where
  height := fun _ => 0
  le_height := fun _ x hx => finiteLogShellSet_nonneg hx
  mem_of_le_height := fun _ x hx _ => hx

theorem finitePacketAttainedCut_nonempty
    (P : SourceLGPProcession l Label Choice) :
    Nonempty (AttainedHullCut (finitePacketModel P) finiteLogShellSet) :=
  ⟨finitePacketAttainedCut P⟩

/-- The witness is exactly the frozen attainment predicate. -/
theorem finitePacketModel_familyCutAttainedIn
    (P : SourceLGPProcession l Label Choice) :
    FamilyCutAttainedIn finiteLogShellSet (finitePacketModel P).possibleImage :=
  (nonempty_attainedHullCut_iff_familyCutAttainedIn (finitePacketModel P)
    finiteLogShellSet).mp (finitePacketAttainedCut_nonempty P)

/-! ## 3. The three conditions of the attainment-slot criterion -/

theorem finitePacketModel_contained
    (P : SourceLGPProcession l Label Choice) :
    ∀ c, (finitePacketModel P).possibleImage c ⊆ finiteLogShellSet :=
  fun _ => subset_rfl

theorem finitePacketModel_directed
    (P : SourceLGPProcession l Label Choice) :
    PossibleImageDirected (finitePacketModel P) := by
  intro c c'
  exact ⟨c, subset_rfl, subset_rfl⟩

theorem finitePacketModel_upClosedIn
    (P : SourceLGPProcession l Label Choice) :
    PossibleImageUpClosedIn (finitePacketModel P) finiteLogShellSet := by
  intro c x _ y hy _
  exact hy

theorem finitePacketModel_logShellRayPresentation
    (P : SourceLGPProcession l Label Choice) :
    LogShellRayPresentation (finitePacketModel P) finiteLogShellSet
      (finitePacketAttainedCut P).height := by
  intro c
  ext x
  constructor
  · intro hx
    exact ⟨hx, finiteLogShellSet_nonneg hx⟩
  · rintro ⟨hx, -⟩
    exact hx

/-- The criterion's forward direction at the finite model: the ray
presentation yields directedness, up-closure, and the two height laws. -/
theorem finitePacketModel_threeConditions
    (P : SourceLGPProcession l Label Choice) :
    PossibleImageDirected (finitePacketModel P) ∧
      PossibleImageUpClosedIn (finitePacketModel P) finiteLogShellSet ∧
      (∀ c, ∀ x : Real, x ∈ (finitePacketModel P).possibleImage c →
        (finitePacketAttainedCut P).height c ≤ x) ∧
      (∀ c, ∀ x : Real, x ∈ finiteLogShellSet →
        (finitePacketAttainedCut P).height c ≤ x →
        x ∈ (finitePacketModel P).possibleImage c) :=
  (logShellRayPresentation_iff_directed_upClosedIn_attained
    (Q := finitePacketModel P) finiteLogShellSet
    (finitePacketAttainedCut P).height
    (finitePacketModel_contained P)).mp
    (finitePacketModel_logShellRayPresentation P)

/-- The criterion's converse direction at the finite model: the three
conditions rebuild the ray presentation. -/
theorem finitePacketModel_logShellRayPresentation_of_threeConditions
    (P : SourceLGPProcession l Label Choice) :
    LogShellRayPresentation (finitePacketModel P) finiteLogShellSet
      (finitePacketAttainedCut P).height :=
  (logShellRayPresentation_iff_directed_upClosedIn_attained
    (Q := finitePacketModel P) finiteLogShellSet
    (finitePacketAttainedCut P).height
    (finitePacketModel_contained P)).mpr
    ⟨finitePacketModel_directed P, finitePacketModel_upClosedIn P,
      (finitePacketAttainedCut P).le_height,
      (finitePacketAttainedCut P).mem_of_le_height⟩

/-! ## 4. Route 1 variant: `L = Set.univ` with the ray `[0, +inf)` -/

/-- The ray packet realization: constant possible-image family `Set.Ici 0`. -/
noncomputable def univRayPacketModel (P : SourceLGPProcession l Label Choice) :
    SourcePacketRealization.{u, v, 0} P where
  carrier := fun _ => PUnit
  distinguished := fun _ => PUnit.unit
  logVolume := fun _ => 0
  determinant := fun _ => 1
  determinant_positive := fun _ => by norm_num
  log_determinant := fun _ => Real.log_one
  possibleImage := fun _ => Set.Ici (0 : Real)
  possibleImage_nonempty := fun _ => ⟨0, Set.mem_Ici.mpr le_rfl⟩
  ind1_volume := fun _ _ => rfl
  ind2_volume := fun _ _ => rfl
  ind3_volume := fun _ _ => le_rfl
  ind1_determinant := fun _ _ => rfl
  ind2_determinant := fun _ _ => rfl
  ind3_determinant := fun _ _ => le_rfl
  image_ind1 := fun _ _ => rfl
  image_ind2 := fun _ _ => rfl
  image_ind3 := fun _ _ z hz => ⟨z, hz, le_rfl⟩

noncomputable def univRayAttainedCut
    (P : SourceLGPProcession l Label Choice) :
    AttainedHullCut (univRayPacketModel P) Set.univ where
  height := fun _ => 0
  le_height := fun _ x hx => Set.mem_Ici.mp hx
  mem_of_le_height := fun _ x _ hx => Set.mem_Ici.mpr hx

theorem univRayAttainedCut_nonempty
    (P : SourceLGPProcession l Label Choice) :
    Nonempty (AttainedHullCut (univRayPacketModel P) Set.univ) :=
  ⟨univRayAttainedCut P⟩

theorem univRay_logShellRayPresentation
    (P : SourceLGPProcession l Label Choice) :
    LogShellRayPresentation (univRayPacketModel P) Set.univ
      (univRayAttainedCut P).height := by
  intro c
  ext x
  constructor
  · intro hx
    exact ⟨Set.mem_univ x, hx⟩
  · rintro ⟨-, hx⟩
    exact hx

/-- The criterion at the `L = Set.univ` variant. -/
theorem univRay_threeConditions
    (P : SourceLGPProcession l Label Choice) :
    PossibleImageDirected (univRayPacketModel P) ∧
      PossibleImageUpClosedIn (univRayPacketModel P) Set.univ ∧
      (∀ c, ∀ x : Real, x ∈ (univRayPacketModel P).possibleImage c →
        (univRayAttainedCut P).height c ≤ x) ∧
      (∀ c, ∀ x : Real, x ∈ Set.univ →
        (univRayAttainedCut P).height c ≤ x →
        x ∈ (univRayPacketModel P).possibleImage c) :=
  (logShellRayPresentation_iff_directed_upClosedIn_attained
    (Q := univRayPacketModel P) Set.univ
    (univRayAttainedCut P).height
    (fun _ _ _ => Set.mem_univ _)).mp
    (univRay_logShellRayPresentation P)

/-! ## 5. Route 3 boundary contrast: separated singletons -/

/-- The separated-singleton family `false ↦ {0}`, `true ↦ {1}`. -/
def twoSingletonFamily (b : Bool) : Set Real :=
  if b = false then {0} else {1}

theorem not_familyDirected_twoSingletonFamily :
    ¬ FamilyDirected twoSingletonFamily := by
  intro hdir
  obtain ⟨k, h0sub, h1sub⟩ := hdir false true
  have hk0 : (0 : Real) ∈ twoSingletonFamily k :=
    h0sub (by simp [twoSingletonFamily])
  have hk1 : (1 : Real) ∈ twoSingletonFamily k :=
    h1sub (by simp [twoSingletonFamily])
  cases k
  · simp [twoSingletonFamily] at hk1
  · simp [twoSingletonFamily] at hk0

theorem not_familyCutAttainedIn_twoSingletonFamily :
    ¬ FamilyCutAttainedIn Set.univ twoSingletonFamily := by
  rintro ⟨m, hlow, hcof⟩
  have h0 : m false ≤ (0 : Real) := hlow false 0 (by simp [twoSingletonFamily])
  have hmem : (1 : Real) ∈ twoSingletonFamily false :=
    hcof false 1 (Set.mem_univ 1) (le_trans h0 zero_le_one)
  simp [twoSingletonFamily] at hmem

end HullPresentationAdoption

end

end K1K2Realization

namespace Audit

/-- Finite-model supply for the attained hull cut: concrete inhabitants of
`AttainedHullCut` over an arbitrary frozen packet interface, with the three
conditions of the attainment-slot criterion verified against the frozen
theorem.  Carries no claim about the actual IUT packet (see the module
docstring's faithfulness boundary). -/
def attainedHullCutFiniteModel : Obligation where
  id := "IUT-III.attained-hull-cut-finite-model"
  source :=
    "IUT III, Theorem 3.11 context; McClintock hull-presentation finite models"
  status := VerificationStatus.provedKernel
  note :=
    "Concrete finite models of AttainedHullCut over an arbitrary frozen " ++
      "SourceLGPProcession: constant possibleImage = {0,1,2} with " ++
      "L = range (Fin 3), and constant ray Ici 0 with L = univ; directed, " ++
      "up-closed and attained verified through " ++
      "logShellRayPresentation_iff_directed_upClosedIn_attained. Two-singleton " ++
      "family gives the boundary contrast (neither directed nor attained). " ++
      "Model instance only: not the source-level hpres of the actual packet."
  dependsOn := [ "IUT-III.k1k2-hull-presentation-adoption" ]

end Audit

end LeanFormal.IUT

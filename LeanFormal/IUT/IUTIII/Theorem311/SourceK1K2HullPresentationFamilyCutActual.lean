import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2HullPresentationAdoption
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2HullPresentationModel
import LeanFormal.IUT.IUTIII.Theorem311.SourceCompletionK1K2Wiring
import Mathlib.Tactic

/-!
# Attainment of the hull cut for actual packets: exact conditions and a ray packet

Run family-cut-actual-20261017.  New file; no existing source file is modified.

The adoption package freezes the attainment slot
FamilyCutAttainedIn L Q.possibleImage and proves that, under containment of the
possible images in L, it is equivalent to the existence of a log-shell ray
presentation.  The packet-instance package proves that the frozen packet laws
alone do not imply the slot: the separated-singleton packet satisfies every law
but has no attained hull cut at L = Set.univ.  This file advances the actual
packet side in two directions.

1. Exact characterization.  For any nonempty family S of real sets,

     FamilyCutAttainedIn L S  iff
       FamilyUpClosedIn L S
       and every S c is bounded below
       and sInf (S c) belongs to S c whenever sInf (S c) belongs to L.

   No containment S c subset L is needed.  The third condition is exactly the
   missing attachment of the lower boundary: the open-ray family is up-closed
   and bounded below but fails it, while the separated-singleton family fails
   up-closure.  Hence the characterization is sharp at the frozen interface.

2. A concrete non-vacuous ray packet.  For any actual packet Q, the packet
   negLogVolumeRayPacket Q keeps the carrier, distinguished points, log-volume
   and determinant of Q and replaces the possible images by the closed rays
   Set.Ici (-Q.logVolume c).  Every field of SourcePacketRealization is proved.
   The sign is chosen so that the Ind3 volume inequality becomes the consumer
   inequality height (ind3 m c) <= height c.  Its images are proper infinite
   rays, its log-shell set is the union of these rays (not Set.univ by fiat),
   and it has a proved FamilyCutAttainedIn, an AttainedHullCut, the containment
   hsub, and the log-shell ray presentation.

3. Actual completion packet.  For the supplied packet C.packet of
   SourceTheorem311Completion, the attainment slot is characterized exactly by
   the same three conditions, both for an arbitrary ambient L and for the
   canonical ambient set possibleImageUnion C.packet.  Thus the remaining
   source obligation is precisely: up-closure of the actual images, boundedness
   below, and attachment of their infima inside L.

Truth boundary.  SourceTheorem311Completion is an explicit parameter; the
D3--D11 source gate is not closed here.  The ray packet is an alternative
packet derived from the actual log-volume and determinant, not a proof that the
original possibleImage family of the paper has the attainment property.  No
statement about the original IUT text is asserted beyond the frozen interfaces.
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
open HullPresentationAdoption

namespace HullPresentationFamilyCutActual

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

noncomputable section

/-! ## 1. Exact characterization of the attainment slot -/

section Abstract

variable {σ : Type*}

/-- Attainment of the hull cut is equivalent to three explicit properties of
the family: up-closure in the ambient set, boundedness below, and attachment of
the infimum whenever that infimum lies in the ambient set.  Containment of the
members in the ambient set is not needed. -/
theorem familyCutAttainedIn_iff_upClosedIn_and_sInf_mem
    {L : Set Real} {S : σ → Set Real}
    (hne : ∀ c, (S c).Nonempty) :
    FamilyCutAttainedIn L S ↔
      FamilyUpClosedIn L S ∧
        (∀ c, BddBelow (S c)) ∧
        (∀ c, sInf (S c) ∈ L → sInf (S c) ∈ S c) := by
  constructor
  · rintro ⟨m, hlow, hcof⟩
    refine ⟨?_, ?_, ?_⟩
    · intro c x hx y hyL hxy
      exact hcof c y hyL (le_trans (hlow c x hx) hxy)
    · intro c
      exact ⟨m c, fun x hx => hlow c x hx⟩
    · intro c hmem
      exact hcof c (sInf (S c)) hmem
        (le_csInf (hne c) (fun x hx => hlow c x hx))
  · rintro ⟨hup, hbdd, hsInf⟩
    refine ⟨fun c => sInf (S c), ?_, ?_⟩
    · intro c x hx
      exact csInf_le (hbdd c) hx
    · intro c x hxL hx
      rcases lt_or_eq_of_le hx with hlt | heq
      · obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt (hne c) hlt
        exact hup c y hy x hxL hyx.le
      · change sInf (S c) = x at heq
        rw [← heq]
        exact hsInf c (by rwa [heq])

/-- The open-boundary case: if no infimum lies in the ambient set, up-closure
and boundedness below already give attainment. -/
theorem familyCutAttainedIn_of_upClosedIn_and_sInf_not_mem
    {L : Set Real} {S : σ → Set Real}
    (hne : ∀ c, (S c).Nonempty)
    (hup : FamilyUpClosedIn L S)
    (hbdd : ∀ c, BddBelow (S c))
    (hnot : ∀ c, sInf (S c) ∉ L) :
    FamilyCutAttainedIn L S := by
  refine ⟨fun c => sInf (S c), ?_, ?_⟩
  · intro c x hx
    exact csInf_le (hbdd c) hx
  · intro c x hxL hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt (hne c) hlt
      exact hup c y hy x hxL hyx.le
    · change sInf (S c) = x at heq
      exact absurd (by rw [heq]; exact hxL) (hnot c)

/-- The closed-image case: if every infimum is attained in its member, then
up-closure and boundedness below give attainment. -/
theorem familyCutAttainedIn_of_upClosedIn_and_sInf_mem
    {L : Set Real} {S : σ → Set Real}
    (hne : ∀ c, (S c).Nonempty)
    (hup : FamilyUpClosedIn L S)
    (hbdd : ∀ c, BddBelow (S c))
    (hmem : ∀ c, sInf (S c) ∈ S c) :
    FamilyCutAttainedIn L S := by
  refine ⟨fun c => sInf (S c), ?_, ?_⟩
  · intro c x hx
    exact csInf_le (hbdd c) hx
  · intro c x hxL hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt (hne c) hlt
      exact hup c y hy x hxL hyx.le
    · rw [← heq]
      exact hmem c

end Abstract

section Packet

variable {P : SourceLGPProcession l Label Choice}

/-- Packet form of the exact characterization, with the packet's own
nonemptiness law. -/
theorem packet_familyCutAttainedIn_iff_upClosedIn_and_sInf_mem
    (Q : SourcePacketRealization P) (L : Set Real) :
    FamilyCutAttainedIn L Q.possibleImage ↔
      FamilyUpClosedIn L Q.possibleImage ∧
        (∀ c, BddBelow (Q.possibleImage c)) ∧
        (∀ c, sInf (Q.possibleImage c) ∈ L →
          sInf (Q.possibleImage c) ∈ Q.possibleImage c) :=
  familyCutAttainedIn_iff_upClosedIn_and_sInf_mem Q.possibleImage_nonempty

/-- The canonical ambient set determined by the packet: the union of its
possible images.  Containment in this set is definitional, so the attainment
question on this set carries no separate hsub obligation. -/
def possibleImageUnion (Q : SourcePacketRealization P) : Set Real :=
  ⋃ c, Q.possibleImage c

theorem possibleImage_subset_union
    (Q : SourcePacketRealization P) (c : Choice) :
    Q.possibleImage c ⊆ possibleImageUnion Q :=
  Set.subset_iUnion (fun c => Q.possibleImage c) c

/-- Exact form on the canonical ambient set: the attainment slot is equivalent
to up-closure, boundedness below, and attachment of the infima. -/
theorem packet_familyCutAttainedIn_union_iff
    (Q : SourcePacketRealization P) :
    FamilyCutAttainedIn (possibleImageUnion Q) Q.possibleImage ↔
      FamilyUpClosedIn (possibleImageUnion Q) Q.possibleImage ∧
        (∀ c, BddBelow (Q.possibleImage c)) ∧
        (∀ c, sInf (Q.possibleImage c) ∈ possibleImageUnion Q →
          sInf (Q.possibleImage c) ∈ Q.possibleImage c) :=
  packet_familyCutAttainedIn_iff_upClosedIn_and_sInf_mem Q _

/-! ## 2. The closed negated-log-volume ray packet -/

/-- The ray packet associated to an actual packet: carrier, distinguished
points, log-volume and determinant are those of Q, while the possible image at
c is the closed ray Set.Ici (-Q.logVolume c).  The sign is chosen so that the
Ind3 volume inequality becomes the consumer inequality
height (ind3 m c) <= height c. -/
noncomputable def negLogVolumeRayPacket
    (Q : SourcePacketRealization P) : SourcePacketRealization P where
  carrier := Q.carrier
  distinguished := Q.distinguished
  logVolume := Q.logVolume
  determinant := Q.determinant
  determinant_positive := Q.determinant_positive
  log_determinant := Q.log_determinant
  possibleImage := fun c => Set.Ici (-Q.logVolume c)
  possibleImage_nonempty := fun c =>
    ⟨-Q.logVolume c, Set.mem_Ici.mpr le_rfl⟩
  ind1_volume := Q.ind1_volume
  ind2_volume := Q.ind2_volume
  ind3_volume := Q.ind3_volume
  ind1_determinant := Q.ind1_determinant
  ind2_determinant := Q.ind2_determinant
  ind3_determinant := Q.ind3_determinant
  image_ind1 := by
    intro g c
    rw [Q.ind1_volume g c]
  image_ind2 := by
    intro g c
    rw [Q.ind2_volume g c]
  image_ind3 := by
    intro n c z hz
    exact ⟨z, Set.mem_Ici.mpr
      (le_trans (neg_le_neg (Q.ind3_volume n c)) (Set.mem_Ici.mp hz)), le_rfl⟩

@[simp] theorem negLogVolumeRayPacket_possibleImage
    (Q : SourcePacketRealization P) (c : Choice) :
    (negLogVolumeRayPacket Q).possibleImage c = Set.Ici (-Q.logVolume c) := rfl

/-- The log-shell set generated by the ray packet: the union of its possible
images.  It is not imposed to be Set.univ. -/
noncomputable def negLogVolumeRayLogShellSet
    (Q : SourcePacketRealization P) : Set Real :=
  ⋃ c, Set.Ici (-Q.logVolume c)

theorem negLogVolumeRayPacket_image_subset_logShellSet
    (Q : SourcePacketRealization P) (c : Choice) :
    (negLogVolumeRayPacket Q).possibleImage c ⊆
      negLogVolumeRayLogShellSet Q := by
  rw [negLogVolumeRayPacket_possibleImage]
  exact Set.subset_iUnion (fun c => Set.Ici (-Q.logVolume c)) c

/-- Non-vacuity: no possible image of the ray packet is the whole real line. -/
theorem negLogVolumeRayPacket_possibleImage_ne_univ
    (Q : SourcePacketRealization P) (c : Choice) :
    (negLogVolumeRayPacket Q).possibleImage c ≠ Set.univ := by
  intro h
  have hmem : -Q.logVolume c - 1 ∈ (negLogVolumeRayPacket Q).possibleImage c := by
    rw [h]
    exact Set.mem_univ _
  rw [negLogVolumeRayPacket_possibleImage] at hmem
  have hle := Set.mem_Ici.mp hmem
  linarith

/-- Non-vacuity: every possible image of the ray packet is infinite. -/
theorem negLogVolumeRayPacket_possibleImage_infinite
    (Q : SourcePacketRealization P) (c : Choice) :
    ((negLogVolumeRayPacket Q).possibleImage c).Infinite := by
  rw [negLogVolumeRayPacket_possibleImage]
  exact Set.Ici_infinite _

/-- The ray packet attains its hull cut on the log-shell set generated by its
own images. -/
theorem negLogVolumeRayPacket_familyCutAttainedIn
    (Q : SourcePacketRealization P) :
    FamilyCutAttainedIn (negLogVolumeRayLogShellSet Q)
      (negLogVolumeRayPacket Q).possibleImage := by
  refine ⟨fun c => -Q.logVolume c, ?_, ?_⟩
  · intro c x hx
    rw [negLogVolumeRayPacket_possibleImage] at hx
    exact Set.mem_Ici.mp hx
  · intro c x _ hx
    rw [negLogVolumeRayPacket_possibleImage]
    exact Set.mem_Ici.mpr hx

/-- The same ray packet attains its hull cut on Set.univ; the packet itself is
still non-vacuous, since all its images are proper infinite rays. -/
theorem negLogVolumeRayPacket_familyCutAttainedIn_univ
    (Q : SourcePacketRealization P) :
    FamilyCutAttainedIn Set.univ (negLogVolumeRayPacket Q).possibleImage := by
  refine ⟨fun c => -Q.logVolume c, ?_, ?_⟩
  · intro c x hx
    rw [negLogVolumeRayPacket_possibleImage] at hx
    exact Set.mem_Ici.mp hx
  · intro c x _ hx
    rw [negLogVolumeRayPacket_possibleImage]
    exact Set.mem_Ici.mpr hx

/-- The concrete attainment witness of the ray packet. -/
noncomputable def negLogVolumeRayAttainedHullCut
    (Q : SourcePacketRealization P) :
    AttainedHullCut (negLogVolumeRayPacket Q) (negLogVolumeRayLogShellSet Q) where
  height := fun c => -Q.logVolume c
  le_height := fun c x hx => by
    rw [negLogVolumeRayPacket_possibleImage] at hx
    exact Set.mem_Ici.mp hx
  mem_of_le_height := fun c x _ hx => by
    rw [negLogVolumeRayPacket_possibleImage]
    exact Set.mem_Ici.mpr hx

theorem negLogVolumeRayAttainedHullCut_nonempty
    (Q : SourcePacketRealization P) :
    Nonempty (AttainedHullCut (negLogVolumeRayPacket Q)
      (negLogVolumeRayLogShellSet Q)) :=
  ⟨negLogVolumeRayAttainedHullCut Q⟩

/-- The ray presentation of the ray packet, obtained from its attainment
witness and the proved containment. -/
theorem negLogVolumeRay_logShellRayPresentation
    (Q : SourcePacketRealization P) :
    LogShellRayPresentation (negLogVolumeRayPacket Q)
      (negLogVolumeRayLogShellSet Q)
      (negLogVolumeRayAttainedHullCut Q).height :=
  logShellRayPresentation_of_attainedHullCut (negLogVolumeRayPacket Q)
    (negLogVolumeRayLogShellSet Q)
    (negLogVolumeRayPacket_image_subset_logShellSet Q)
    (negLogVolumeRayAttainedHullCut Q)

/-- The attained height satisfies the consumer's Ind3 monotonicity direction. -/
theorem negLogVolumeRayAttainedHullCut_hind3
    (Q : SourcePacketRealization P) (m : Nat) (c : Choice) :
    (negLogVolumeRayAttainedHullCut Q).height (P.ind3 m c) ≤
      (negLogVolumeRayAttainedHullCut Q).height c := by
  change -Q.logVolume (P.ind3 m c) ≤ -Q.logVolume c
  exact neg_le_neg (Q.ind3_volume m c)

end Packet

/-! ## 3. The actual completion packet -/

section Completion

variable (C : SourceTheorem311Completion.{u, v, w} l Label Choice)

/-- Exact characterization of the attainment slot for the supplied actual
packet, at an arbitrary ambient log-shell set. -/
theorem completionPacket_familyCutAttainedIn_iff_upClosedIn_and_sInf_mem
    (L : Set Real) :
    FamilyCutAttainedIn L C.packet.possibleImage ↔
      FamilyUpClosedIn L C.packet.possibleImage ∧
        (∀ c, BddBelow (C.packet.possibleImage c)) ∧
        (∀ c, sInf (C.packet.possibleImage c) ∈ L →
          sInf (C.packet.possibleImage c) ∈ C.packet.possibleImage c) :=
  packet_familyCutAttainedIn_iff_upClosedIn_and_sInf_mem C.packet L

/-- Exact characterization on the canonical ambient set of the actual packet;
the containment hsub is definitional here. -/
theorem completionPacket_familyCutAttainedIn_union_iff :
    FamilyCutAttainedIn (possibleImageUnion C.packet) C.packet.possibleImage ↔
      FamilyUpClosedIn (possibleImageUnion C.packet) C.packet.possibleImage ∧
        (∀ c, BddBelow (C.packet.possibleImage c)) ∧
        (∀ c, sInf (C.packet.possibleImage c) ∈ possibleImageUnion C.packet →
          sInf (C.packet.possibleImage c) ∈ C.packet.possibleImage c) :=
  packet_familyCutAttainedIn_union_iff C.packet

/-- Sufficient form for the actual packet: the three explicit conditions give
the nonempty attainment witness. -/
theorem completionPacket_nonempty_attainedHullCut_of_conditions
    (L : Set Real)
    (hup : FamilyUpClosedIn L C.packet.possibleImage)
    (hbdd : ∀ c, BddBelow (C.packet.possibleImage c))
    (hsInf : ∀ c, sInf (C.packet.possibleImage c) ∈ L →
      sInf (C.packet.possibleImage c) ∈ C.packet.possibleImage c) :
    Nonempty (AttainedHullCut C.packet L) :=
  (nonempty_attainedHullCut_iff_familyCutAttainedIn C.packet L).mpr
    ((packet_familyCutAttainedIn_iff_upClosedIn_and_sInf_mem C.packet L).mpr
      ⟨hup, hbdd, hsInf⟩)

/-- The ray packet built from the actual completion packet attains its hull cut
on the log-shell set generated by its own images. -/
theorem completionPacket_negLogVolumeRay_familyCutAttainedIn :
    FamilyCutAttainedIn (negLogVolumeRayLogShellSet C.packet)
      (negLogVolumeRayPacket C.packet).possibleImage :=
  negLogVolumeRayPacket_familyCutAttainedIn C.packet

/-- The corresponding containment hsub for the actual ray packet. -/
theorem completionPacket_negLogVolumeRay_image_subset :
    ∀ c, (negLogVolumeRayPacket C.packet).possibleImage c ⊆
      negLogVolumeRayLogShellSet C.packet :=
  negLogVolumeRayPacket_image_subset_logShellSet C.packet

/-- The actual ray packet has a concrete attainment witness. -/
theorem completionPacket_negLogVolumeRay_nonempty_attainedHullCut :
    Nonempty (AttainedHullCut (negLogVolumeRayPacket C.packet)
      (negLogVolumeRayLogShellSet C.packet)) :=
  negLogVolumeRayAttainedHullCut_nonempty C.packet

/-- Non-vacuity of the actual ray packet: its images are proper subsets of the
real line. -/
theorem completionPacket_negLogVolumeRay_possibleImage_ne_univ (c : Choice) :
    (negLogVolumeRayPacket C.packet).possibleImage c ≠ Set.univ :=
  negLogVolumeRayPacket_possibleImage_ne_univ C.packet c

/-- The actual ray packet also attains its hull cut on Set.univ. -/
theorem completionPacket_negLogVolumeRay_familyCutAttainedIn_univ :
    FamilyCutAttainedIn Set.univ
      (negLogVolumeRayPacket C.packet).possibleImage :=
  negLogVolumeRayPacket_familyCutAttainedIn_univ C.packet

end Completion

/-! ## 4. Sharpness at the frozen counterexamples -/

section Sharpness

theorem openRayFamily_upClosedIn_univ :
    FamilyUpClosedIn Set.univ openRayFamily :=
  familyUpClosedIn_univ_openRayFamily

theorem openRayFamily_bddBelow (b : Bool) : BddBelow (openRayFamily b) := by
  cases b
  · refine ⟨0, ?_⟩
    intro x hx
    simp [openRayFamily] at hx
    linarith
  · refine ⟨-1, ?_⟩
    intro x hx
    simp [openRayFamily] at hx
    linarith

/-- The open-ray family fails exactly the infimum-attachment condition: its
infimum lies in Set.univ but not in the open ray. -/
theorem openRayFamily_sInf_mem_condition_fails :
    ¬ (∀ b : Bool, sInf (openRayFamily b) ∈ Set.univ →
      sInf (openRayFamily b) ∈ openRayFamily b) := by
  intro h
  have hmem := h false (Set.mem_univ _)
  have h0 : sInf (openRayFamily false) = (0 : Real) := by
    simp [openRayFamily, csInf_Ioi]
  rw [h0] at hmem
  simp [openRayFamily] at hmem

/-- The open-ray family satisfies the other two conditions, so the third is
the precise missing one. -/
theorem openRayFamily_fails_only_sInf_condition :
    FamilyUpClosedIn Set.univ openRayFamily ∧
      (∀ b, BddBelow (openRayFamily b)) ∧
      ¬ (∀ b : Bool, sInf (openRayFamily b) ∈ Set.univ →
        sInf (openRayFamily b) ∈ openRayFamily b) :=
  ⟨openRayFamily_upClosedIn_univ, openRayFamily_bddBelow,
    openRayFamily_sInf_mem_condition_fails⟩

theorem twoSingletonFamily_bddBelow (b : Bool) :
    BddBelow (twoSingletonFamily b) := by
  cases b
  · refine ⟨0, ?_⟩
    intro x hx
    simp [twoSingletonFamily] at hx
    linarith
  · refine ⟨1, ?_⟩
    intro x hx
    simp [twoSingletonFamily] at hx
    linarith

theorem twoSingletonFamily_sInf_mem (b : Bool) :
    sInf (twoSingletonFamily b) ∈
      twoSingletonFamily b := by
  cases b
  · simp [twoSingletonFamily]
  · simp [twoSingletonFamily]

/-- The separated-singleton family fails up-closure: 0 lies in the first
singleton, 1 lies in Set.univ and dominates 0, but 1 is not in the singleton. -/
theorem twoSingletonFamily_not_upClosedIn_univ :
    ¬ FamilyUpClosedIn Set.univ twoSingletonFamily := by
  intro h
  have h0 : (0 : Real) ∈ twoSingletonFamily false := by
    simp [twoSingletonFamily]
  have h1 := h false 0 h0 1 (Set.mem_univ 1) (by norm_num : (0 : Real) ≤ 1)
  simp [twoSingletonFamily] at h1

/-- The separated-singleton family satisfies the other two conditions, so
up-closure is the precise missing one there. -/
theorem twoSingletonFamily_fails_only_upClosed :
    ¬ FamilyUpClosedIn Set.univ twoSingletonFamily ∧
      (∀ b, BddBelow (twoSingletonFamily b)) ∧
      (∀ b, sInf (twoSingletonFamily b) ∈
        twoSingletonFamily b) :=
  ⟨twoSingletonFamily_not_upClosedIn_univ, twoSingletonFamily_bddBelow,
    twoSingletonFamily_sInf_mem⟩

end Sharpness

end

end HullPresentationFamilyCutActual

end K1K2Realization

end LeanFormal.IUT

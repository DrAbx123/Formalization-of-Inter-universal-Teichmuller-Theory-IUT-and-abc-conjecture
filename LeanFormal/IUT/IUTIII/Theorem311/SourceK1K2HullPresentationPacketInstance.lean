import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2HullPresentationAdoption
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionFromContract

/-!
# Packet instance for the attained hull-cut slot: separated singletons

Run `source-k1k2-packet-instance-20261017`.  New file; no existing source
file is modified.

The adoption package `SourceK1K2HullPresentationAdoption.lean` freezes the
witness type `AttainedHullCut Q L`, the criterion
`logShellRayPresentation_iff_directed_upClosedIn_attained`, the gap card
`HullCutAttainmentGap Q L`, and the two-singleton separation
`not_hullCutAttainmentGap_of_two_singletonImages`.  The finite-model file
`SourceK1K2HullPresentationModel.lean` supplies inhabitants of the witness
type over synthetic constant families, but it gives no packet-level
nonemptiness theorem and no counterexample carried by the packet laws.

This file answers the packet-side question for the general form of the
laws: they do not imply the attained hull cut.  Over the
canonical identity procession `sourceLGPProcessionOfDefinition31Data S base`
of `SourceProcessionFromContract.lean`, the packet
`separatedSingletonPacket S base` has `Choice = Nat`, constant log-volume
`0` and determinant `1`, and the separated-singleton possible-image family
`c ↦ {(c : Real)}`.  Every field of `SourcePacketRealization` holds because
all three procession injections are the identity.  Nevertheless

* `separatedSingletonPacket_not_hullCutAttainmentGap` proves that the gap
  card `HullCutAttainmentGap Q Set.univ` is empty, and
* `separatedSingletonPacket_not_nonempty_attainedHullCut` is the same
  statement in the witness-type form.

The containment `hsub : ∀ c, Q.possibleImage c ⊆ Set.univ` is definitional,
so the failure is not caused by a missing containment hypothesis.  Hence the
frozen `SourceLGPProcession` and `SourcePacketRealization` laws do not imply
the attained hull cut, even in the presence of `hsub`.

The precise extra law is the attainment slot itself:
`FamilyCutAttainedIn L Q.possibleImage`, equivalently the ray presentation
`∃ h, LogShellRayPresentation Q L h` under `hsub`.  The sufficiency half is
recorded below as `nonempty_attainedHullCut_of_familyCutAttainedIn`; it is the
frozen equivalence `nonempty_attainedHullCut_iff_familyCutAttainedIn`.  This
file does not manufacture that law for the actual IUT packet.

Truth boundary: `S : SourceDefinition31Data l` is supplied as a parameter.
The D3-D11 source gate is not closed here and no arithmetic source datum is
constructed.  The procession and the packet are otherwise concrete; nothing
below asserts anything about the arithmetic possible-image family of the
paper's packet.
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

noncomputable section

namespace HullPresentationPacketInstance

/-! ## 1. The separated-singleton packet over the identity procession -/

/-- The packet whose possible-image family is the separated-singleton family
`c ↦ {(c : Real)}`, over the canonical identity procession built from a
supplied Definition 3.1 source datum.  The carrier is `PUnit`, the log-volume
is `0`, and the determinant is `1`; the three procession injections are the
identity, so every `SourcePacketRealization` law holds definitionally. -/
def separatedSingletonPacket {l : PrimeGeFive} {Label : Type u}
    [AddGroup Label] (S : SourceDefinition31Data.{u} l) (base : Nat) :
    SourcePacketRealization
      (_root_.LeanFormal.IUT.SourceProcessionAttack.sourceLGPProcessionOfDefinition31Data
        (Label := Label) (Choice := Nat) S base) where
  carrier := fun _ => PUnit
  distinguished := fun _ => PUnit.unit
  logVolume := fun _ => 0
  determinant := fun _ => 1
  determinant_positive := fun _ => zero_lt_one
  log_determinant := fun _ => Real.log_one
  possibleImage := fun c => {(c : Real)}
  possibleImage_nonempty := fun c => ⟨(c : Real), by simp⟩
  ind1_volume := fun _ _ => rfl
  ind2_volume := fun _ _ => rfl
  ind3_volume := fun _ _ => le_rfl
  ind1_determinant := fun _ _ => rfl
  ind2_determinant := fun _ _ => rfl
  ind3_determinant := fun _ _ => le_rfl
  image_ind1 := fun _ _ => rfl
  image_ind2 := fun _ _ => rfl
  image_ind3 := fun _ _ z hz => ⟨z, hz, le_rfl⟩

/-! ## 2. Emptiness of the attained hull cut for this packet -/

/-- The gap card fails for the separated-singleton packet at `L = Set.univ`.
The two images `possibleImage 0 = {0}` and `possibleImage 1 = {1}` are
separated: an attainment height `height 0` would have to satisfy `height 0 ≤ 0`, and
then `1 ∈ Set.univ` with `height 0 ≤ 1` would be forced back into `{0}`. -/
theorem separatedSingletonPacket_not_hullCutAttainmentGap {l : PrimeGeFive}
    {Label : Type u} [AddGroup Label]
    (S : SourceDefinition31Data.{u} l) (base : Nat) :
    ¬ HullPresentationAdoption.HullCutAttainmentGap
      (separatedSingletonPacket (l := l) (Label := Label) S base) Set.univ :=
  HullPresentationAdoption.not_hullCutAttainmentGap_of_two_singletonImages
    (separatedSingletonPacket (l := l) (Label := Label) S base) Set.univ
    (fun _ _ _ => Set.mem_univ _)
    (c := 0) (c' := 1) (v := 0) (v' := 1)
    zero_lt_one
    (by simp [separatedSingletonPacket])
    (by simp [separatedSingletonPacket])

/-- Packet-level form: the witness type `Nonempty (AttainedHullCut Q L)` is
empty for the separated-singleton packet at `L = Set.univ`, while every
`SourceLGPProcession` and `SourcePacketRealization` field holds. -/
theorem separatedSingletonPacket_not_nonempty_attainedHullCut {l : PrimeGeFive}
    {Label : Type u} [AddGroup Label]
    (S : SourceDefinition31Data.{u} l) (base : Nat) :
    ¬ Nonempty (HullPresentationAdoption.AttainedHullCut
      (separatedSingletonPacket (l := l) (Label := Label) S base) Set.univ) :=
  separatedSingletonPacket_not_hullCutAttainmentGap (Label := Label) S base

/-- The containment hypothesis of the attainment slot is definitional for
this packet at `L = Set.univ`: the emptiness above is not a missing-`hsub`
artifact. -/
theorem separatedSingletonPacket_image_subset_univ {l : PrimeGeFive}
    {Label : Type u} [AddGroup Label]
    (S : SourceDefinition31Data.{u} l) (base : Nat) :
    ∀ c, (separatedSingletonPacket (l := l) (Label := Label) S base).possibleImage c ⊆ Set.univ :=
  fun _ _ _ => Set.mem_univ _

/-! ## 3. The exact extra law -/

/-- The precise missing law: given the containment, the frozen attainment
predicate `FamilyCutAttainedIn L Q.possibleImage` is exactly what produces an
`AttainedHullCut`.  This is the frozen equivalence
`nonempty_attainedHullCut_iff_familyCutAttainedIn`, read in the sufficient
direction; the separated-singleton packet shows that it is not a consequence
of the packet laws. -/
theorem nonempty_attainedHullCut_of_familyCutAttainedIn {l : PrimeGeFive}
    {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (hlaw : FamilyCutAttainedIn L Q.possibleImage) :
    Nonempty (HullPresentationAdoption.AttainedHullCut Q L) :=
  (HullPresentationAdoption.nonempty_attainedHullCut_iff_familyCutAttainedIn Q L).mpr hlaw

end HullPresentationPacketInstance

end

end K1K2Realization

end LeanFormal.IUT

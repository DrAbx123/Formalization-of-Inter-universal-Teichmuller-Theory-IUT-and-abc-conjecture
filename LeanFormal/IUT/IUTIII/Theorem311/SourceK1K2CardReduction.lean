import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Realization
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel
import Mathlib.Tactic

/-!
  # K1/K2 six-card reduction (run k1k2-realization-20261016)

  Attacks the six cards of `k1BoundaryOfLogShellPresentation`
  (`hpres`, `hind3`, `hunbounded`, `hsep`, `hclass`, and the Kummer slot
  `κ`):

  * `hunbounded` and `hsep` are discharged for the canonical choice
    `L = Set.univ` (`upUnbounded_univ`, `raySeparation_univ`);
  * `hind3` is discharged for the canonical decreasing height
    `h = -logVolume` (`negLogVolume_hind3`), from the packet law `ind3_volume`;
  * `κ` is discharged by the identity labelled Kummer iso
    (`labelledKummerIdentity`); the frozen K1 record imposes no law linking
    the Kummer slot to `(P, Q)`;
  * `hclass` is reduced to the volume-translation law
    (`hclass_negLogVolume_iff`) with a proved sufficient condition
    (`hclass_translation_of_shift`), realized by the concrete finite model
    (`normalizedLogVolume_ind3Lift_add`, `normalizedLogVolume_ind3Lift_congr`);
  * `hpres` is separated from the interface: any packet with two strictly
    ordered singleton images admits no ray presentation
    (`not_logShellRayPresentation_of_two_singletonImages`).

  Net reduction: the K1 route needs only the ray law
  `possibleImage c = Set.Ici (-logVolume c)` together with the
  volume-translation card (`k1BoundaryOf_negLogVolumeRayPresentation`); no
  source content is claimed to be proved.
-/

set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe u v

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## κ: identity labelled Kummer iso -/

/-- The identity labelled Kummer iso on any type: identity map and inverse,
constant label.  The frozen K1 record imposes no law relating the Kummer slot
to `(P, Q)`, so this is an admissible inhabitant of the slot. -/
def labelledKummerIdentity (Choice : Type v) : LabelledKummerIso Choice Choice where
  map := id
  inverse := id
  left_inverse := fun _ => rfl
  right_inverse := fun _ => rfl
  label := fun _ => 0
  label_map := fun _ => rfl

theorem labelledKummerIdentity_map (Choice : Type v) (a : Choice) :
    (labelledKummerIdentity Choice).map a = a := rfl

theorem labelledKummerIdentity_inverse (Choice : Type v) (b : Choice) :
    (labelledKummerIdentity Choice).inverse b = b := rfl

/-- The identity labelled Kummer slot family over `Choice`. -/
def labelledKummerIdentityFamily : ∀ _c : Choice, LabelledKummerIso Choice Choice :=
  fun _ => labelledKummerIdentity Choice

/-! ## hunbounded and hsep at `L = Set.univ` -/

theorem upUnbounded_univ : ∀ x : Real, ∃ y ∈ (Set.univ : Set Real), x ≤ y :=
  fun x => ⟨x, Set.mem_univ x, le_rfl⟩

theorem raySeparation_univ : ∀ x y : Real,
    (Set.univ : Set Real) ∩ Set.Ici x = (Set.univ : Set Real) ∩ Set.Ici y → x = y := by
  intro x y h
  have hxy : Set.Ici x = Set.Ici y := by simpa using h
  have h1 : x ∈ Set.Ici y := by
    rw [← hxy]
    exact Set.mem_Ici.mpr (le_refl x)
  have h2 : y ∈ Set.Ici x := by
    rw [hxy]
    exact Set.mem_Ici.mpr (le_refl y)
  exact le_antisymm (Set.mem_Ici.mp h2) (Set.mem_Ici.mp h1)

theorem logShellRayPresentation_univ_iff
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (h : Choice → Real) :
    LogShellRayPresentation Q (Set.univ : Set Real) h ↔
      ∀ c, Q.possibleImage c = Set.Ici (h c) := by
  constructor
  · intro hpres c
    simpa using hpres c
  · intro hray c
    simpa using hray c

/-! ## hind3 at `h = -logVolume` -/

theorem negLogVolume_hind3
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (m : Nat) (c : Choice) :
    -(Q.logVolume (P.ind3 m c)) ≤ -(Q.logVolume c) :=
  neg_le_neg (Q.ind3_volume m c)

/-! ## hclass: reduction and sufficient condition -/

theorem hclass_negLogVolume_iff
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P) :
    (∀ (m : Nat) (c c' : Choice), -(Q.logVolume c) = -(Q.logVolume c') →
      -(Q.logVolume (P.ind3 m c)) = -(Q.logVolume (P.ind3 m c'))) ↔
    (∀ (m : Nat) (c c' : Choice), Q.logVolume c = Q.logVolume c' →
      Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c')) := by
  constructor
  · intro h m c c' hv
    exact neg_inj.mp (h m c c' (congrArg Neg.neg hv))
  · intro h m c c' hv
    exact congrArg Neg.neg (h m c c' (neg_inj.mp hv))

theorem hclass_translation_of_shift
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (shift : Nat → Real)
    (hshift : ∀ m c, Q.logVolume (P.ind3 m c) = Q.logVolume c + shift m) :
    ∀ (m : Nat) (c c' : Choice), Q.logVolume c = Q.logVolume c' →
      Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c') := by
  intro m c c' hv
  rw [hshift m c, hshift m c', hv]

/-! ## bundle reduction -/

def k1BoundaryOf_univRayPresentation
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (h : Choice → Real)
    (hray : ∀ c, Q.possibleImage c = Set.Ici (h c))
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice) :
    K1VerticalBoundary P Q :=
  k1BoundaryOfLogShellPresentation P Q Set.univ h
    (by intro c; simpa using hray c)
    hind3 upUnbounded_univ raySeparation_univ hclass κ

def k1BoundaryOf_negLogVolumeRayPresentation
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hray : ∀ c, Q.possibleImage c = Set.Ici (-(Q.logVolume c)))
    (htrans : ∀ (m : Nat) (c c' : Choice), Q.logVolume c = Q.logVolume c' →
      Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c')) :
    K1VerticalBoundary P Q :=
  k1BoundaryOf_univRayPresentation P Q (fun c => -(Q.logVolume c)) hray
    (fun m c => negLogVolume_hind3 P Q m c)
    (fun m c c' hv => congrArg Neg.neg (htrans m c c' (neg_inj.mp hv)))
    labelledKummerIdentityFamily

def sourceVerticalRealizationOf_negLogVolumeRayPresentation
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hray : ∀ c, Q.possibleImage c = Set.Ici (-(Q.logVolume c)))
    (htrans : ∀ (m : Nat) (c c' : Choice), Q.logVolume c = Q.logVolume c' →
      Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c')) :
    SourceVerticalRealization P Q :=
  (k1BoundaryOf_negLogVolumeRayPresentation P Q hray htrans).toSource

/-! ## hpres separation from the interface -/

theorem not_logShellRayPresentation_of_two_singletonImages
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    {c c' : Choice} {v v' : Real} (hvv' : v < v')
    (hc : Q.possibleImage c = {v}) (hc' : Q.possibleImage c' = {v'}) :
    ¬ LogShellRayPresentation Q L h := by
  intro hpres
  have h1 : v ∈ L ∩ Set.Ici (h c) := by
    rw [← hpres c, hc]
    exact Set.mem_singleton v
  have h2 : v' ∈ L ∩ Set.Ici (h c') := by
    rw [← hpres c', hc']
    exact Set.mem_singleton v'
  have hle : h c ≤ v' := le_trans h1.2 (le_of_lt hvv')
  have hv'mem : v' ∈ L ∩ Set.Ici (h c) := ⟨h2.1, hle⟩
  rw [← hpres c, hc] at hv'mem
  exact (ne_of_gt hvv') (Set.mem_singleton_iff.mp hv'mem)

end

end K1K2Realization

/-! ## Ground instance of the hclass condition in the finite model -/

namespace ConcreteFiniteTheorem311

theorem normalizedLogVolume_ind3Lift_add (l : PrimeGeFive) (n : Nat)
    (c : ProcessionChoice l) :
    normalizedLogVolume l (ProcessionChoice.ind3Lift n c) =
      normalizedLogVolume l c + (n : Real) := by
  rw [normalizedLogVolume, normalizedLogVolume, ProcessionChoice.ind3_upperSemiLevel, Nat.cast_add]
  ring

theorem normalizedLogVolume_ind3Lift_congr (l : PrimeGeFive) (n : Nat)
    {c c' : ProcessionChoice l}
    (hv : normalizedLogVolume l c = normalizedLogVolume l c') :
    normalizedLogVolume l (ProcessionChoice.ind3Lift n c) =
      normalizedLogVolume l (ProcessionChoice.ind3Lift n c') := by
  rw [normalizedLogVolume_ind3Lift_add, normalizedLogVolume_ind3Lift_add, hv]

end ConcreteFiniteTheorem311

end LeanFormal.IUT

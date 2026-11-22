import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2CardReduction
import Mathlib.Tactic

/-!
  # hclass general law: volume-translation law and its exact decomposition
  (run k1k2-realization-20261016, three-artifact package)

  The `hclass` card of `k1BoundaryOfLogShellPresentation` asks that the height
  `h` be constant on the fibers of the log-volume.  For the canonical height
  `h = -logVolume` it is exactly the volume-class law
  (`hclass_negLogVolume_iff`, `SourceK1K2CardReduction`): equal log-volumes
  propagate through the `ind3` family.

  This file attacks the *general* form of the law.

  * The class law over an arbitrary volume datum `(volume, F)` is
    characterized exactly by the fiber-factorization form
    (`VolumeFiberFactorLaw`): each level factors through the volume.
  * The volume-translation law (`VolumeTranslationData`, a single additive
    shift along `ind3`) is decomposed exactly as the class law plus transverse
    (strict-increment) constancy.  Both directions are proved; this is the
    minimal sufficient condition at the data level.
  * The shift is forced to be zero at `0`, additive, nonnegative and monotone
    (frozen interface, using only `ind3_zero`, `ind3_add`, `ind3_volume`).
  * The class law does *not* imply the translation law: an explicit flat
    volume datum (`Bool x Nat`, level-multiplication inside the branch)
    satisfies the class law with non-injective volume and refutes any shift.
    This is the separation witness showing the gap is in the data level.
  * The concrete finite model (`normalizedLogVolume`, `ind3Lift`) satisfies
    the translation law with shift `m |-> m`
    (reuse of `normalizedLogVolume_ind3Lift_add`).

  Status boundary: every statement is about the frozen interfaces (volume
  datum / `(P, Q)`) or the finite model.  No statement of IUT II sections 5-6
  is claimed; in particular no unconditional `hclass` for an arbitrary packet
  is proved, and a frozen-level counterexample would require an inhabitant of
  `SourceLGPProcession` (equivalently `SourceDefinition31Data`-grade source
  arithmetic), which the tree does not have unconditionally.  The data-level
  separation below is the sharpest honest form of the failure of the
  converse implication.
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

/-! ## 1. Volume data: class law, translation law, fiber factorization -/

/-- The volume-class law on a volume datum: two choices with equal volume
receive equal volumes after any `ind3` level.  This is the exact positive form
of the `hclass` card for the canonical height `h = -logVolume`. -/
def VolumeClassLaw {ι : Type*} (volume : ι → Real) (F : Nat → ι → ι) : Prop :=
  ∀ (m : Nat) (c c' : ι), volume c = volume c' → volume (F m c) = volume (F m c')

/-- The volume-translation law on a volume datum: a single additive shift along
the `ind3` family.  The `volumeTranslationLaw_shift_*` theorems below record
the structure forced on the shift by the frozen packet laws. -/
def VolumeTranslationData {ι : Type*} (volume : ι → Real) (F : Nat → ι → ι) : Prop :=
  ∃ shift : Nat → Real, ∀ (m : Nat) (c : ι), volume (F m c) = volume c + shift m

/-- Fiber factorization: the general form of the class law, each level of `F`
factors as a function of the volume alone. -/
def VolumeFiberFactorLaw {ι : Type*} (volume : ι → Real) (F : Nat → ι → ι) : Prop :=
  ∀ m : Nat, ∃ φ : Real → Real, ∀ c : ι, volume (F m c) = φ (volume c)

theorem volumeClassLaw_of_volumeTranslationData {ι : Type*}
    (volume : ι → Real) (F : Nat → ι → ι)
    (h : VolumeTranslationData volume F) :
    VolumeClassLaw volume F := by
  obtain ⟨shift, hs⟩ := h
  intro m c c' hv
  rw [hs m c, hs m c', hv]

/-- Exact general form of the class law: it holds if and only if every level
factors through the volume function.  The backward direction uses classical
choice to select a representative of each volume fiber. -/
theorem volumeFiberFactorLaw_iff_volumeClassLaw {ι : Type*}
    (volume : ι → Real) (F : Nat → ι → ι) :
    VolumeFiberFactorLaw volume F ↔ VolumeClassLaw volume F := by
  constructor
  · intro hF m c c' hv
    obtain ⟨φ, hφ⟩ := hF m
    rw [hφ c, hφ c', hv]
  · intro hclass m
    classical
    refine ⟨fun x => if h : ∃ c, volume c = x then volume (F m h.choose) else 0, ?_⟩
    intro c
    have hc : ∃ c' : ι, volume c' = volume c := ⟨c, rfl⟩
    dsimp only
    rw [dif_pos hc]
    exact (hclass m hc.choose c hc.choose_spec).symm

/-- Exact decomposition of the volume-translation law: a single additive shift
exists if and only if the class law holds and the strict (transverse)
increments of `ind3` are constant.  The class law covers the equal-volume
fibers; the strict-increment constancy is the genuinely additional input. -/
theorem volumeTranslationData_iff_classLaw_and_strictIncrementConstancy
    {ι : Type*} (volume : ι → Real) (F : Nat → ι → ι) (base : ι) :
    VolumeTranslationData volume F ↔
      VolumeClassLaw volume F ∧
        (∀ (m : Nat) (c c' : ι), volume c < volume c' →
          volume (F m c) - volume c = volume (F m c') - volume c') := by
  constructor
  · intro h
    refine ⟨volumeClassLaw_of_volumeTranslationData volume F h, ?_⟩
    obtain ⟨shift, hs⟩ := h
    intro m c c' _
    rw [hs m c, hs m c']
    ring
  · rintro ⟨hclass, hstrict⟩
    classical
    refine ⟨fun m => volume (F m base) - volume base, fun m c => ?_⟩
    have key : volume (F m c) - volume c = volume (F m base) - volume base := by
      rcases lt_trichotomy (volume c) (volume base) with hlt | heq | hgt
      · exact hstrict m c base hlt
      · have := hclass m c base heq
        linarith
      · exact (hstrict m base c hgt).symm
    linarith
/-! ## 2. Separation witness: the class law does not force a shift -/

/-- Volume of the flat model: two branches carrying the same natural levels;
the volume is the level, so it is not injective. -/
def flatVolumeDatumVolume (c : Bool × Nat) : Real := (c.2 : Real)

/-- The `ind3` family of the flat model: multiply the level inside the same
branch. -/
def flatVolumeDatumInd3 (m : Nat) (c : Bool × Nat) : Bool × Nat := (c.1, m * c.2)

/-- The flat model satisfies the class law: the volume of the target depends
only on the level and on `m`. -/
theorem flatVolumeDatum_classLaw :
    VolumeClassLaw flatVolumeDatumVolume flatVolumeDatumInd3 := by
  intro m c c' hv
  have hv' : (c.2 : Real) = (c'.2 : Real) := hv
  have h2 : c.2 = c'.2 := Nat.cast_injective hv'
  change ((m * c.2 : Nat) : Real) = ((m * c'.2 : Nat) : Real)
  rw [h2]

/-- The flat model admits no additive shift: comparing the branch `false` at
levels `0` and `1` at `m = 2` forces `shift 2 = 0` and `shift 2 = 1`. -/
theorem flatVolumeDatum_not_translationData :
    ¬ VolumeTranslationData flatVolumeDatumVolume flatVolumeDatumInd3 := by
  rintro ⟨shift, hs⟩
  have h0 : ((2 * 0 : Nat) : Real) = ((0 : Nat) : Real) + shift 2 := hs 2 (false, 0)
  have h1 : ((2 * 1 : Nat) : Real) = ((1 : Nat) : Real) + shift 2 := hs 2 (false, 1)
  norm_num at h0 h1
  linarith

/-! ## 3. The frozen interface: transfer and the canonical height -/

/-- The class law over the datum `(Q.logVolume, P.ind3)` is exactly the
`hclass` card read positively (no negative sign, no ray data). -/
theorem volumeClassLaw_iff_frozen_hclass
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P) :
    VolumeClassLaw Q.logVolume (fun m c => P.ind3 m c) ↔
      (∀ (m : Nat) (c c' : Choice), Q.logVolume c = Q.logVolume c' →
        Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c')) :=
  Iff.rfl

/-- The frozen form of the translation law. -/
theorem volumeTranslationData_frozen_iff
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P) :
    VolumeTranslationData Q.logVolume (fun m c => P.ind3 m c) ↔
      ∃ shift : Nat → Real, ∀ (m : Nat) (c : Choice),
        Q.logVolume (P.ind3 m c) = Q.logVolume c + shift m :=
  Iff.rfl

/-- Frozen general form of `hclass`: the class law holds if and only if each
`ind3` level factors through the log-volume as a function on `Real`. -/
theorem frozen_hclass_iff_fiberFactorization
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P) :
    (∀ (m : Nat) (c c' : Choice), Q.logVolume c = Q.logVolume c' →
      Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c')) ↔
      (∀ m : Nat, ∃ φ : Real → Real, ∀ c : Choice,
        Q.logVolume (P.ind3 m c) = φ (Q.logVolume c)) :=
  (volumeFiberFactorLaw_iff_volumeClassLaw Q.logVolume
    (fun m c => P.ind3 m c)).symm

/-- Decomposition of the frozen translation law into the class law plus strict
increment constancy; this is the exact minimal sufficient condition recorded
by the hclass card, transported to the frozen interface. -/
theorem frozen_volumeTranslation_iff_classLaw_and_strictIncrement
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P) :
    VolumeTranslationData Q.logVolume (fun m c => P.ind3 m c) ↔
      (∀ (m : Nat) (c c' : Choice), Q.logVolume c = Q.logVolume c' →
        Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c')) ∧
      (∀ (m : Nat) (c c' : Choice), Q.logVolume c < Q.logVolume c' →
        Q.logVolume (P.ind3 m c) - Q.logVolume c =
          Q.logVolume (P.ind3 m c') - Q.logVolume c') :=
  volumeTranslationData_iff_classLaw_and_strictIncrementConstancy
    Q.logVolume (fun m c => P.ind3 m c) P.base

/-- Sufficiency for the canonical height: the translation law implies the
`hclass` card at `h = -logVolume` (`hclass_negLogVolume_iff`).  This is the
proved direction of the reduction assembled in `SourceK1K2CardReduction`. -/
theorem hclass_negLogVolume_of_volumeTranslationLaw
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (shift : Nat → Real)
    (h : ∀ (m : Nat) (c : Choice),
      Q.logVolume (P.ind3 m c) = Q.logVolume c + shift m) :
    ∀ (m : Nat) (c c' : Choice), -(Q.logVolume c) = -(Q.logVolume c') →
      -(Q.logVolume (P.ind3 m c)) = -(Q.logVolume (P.ind3 m c')) := by
  intro m c c' hv
  exact congrArg Neg.neg
    (hclass_translation_of_shift P Q shift h m c c' (neg_inj.mp hv))
/-! ## 4. Structure of the shift forced by the frozen packet laws -/

theorem volumeTranslationLaw_shift_zero
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (shift : Nat → Real)
    (h : ∀ (m : Nat) (c : Choice),
      Q.logVolume (P.ind3 m c) = Q.logVolume c + shift m) :
    shift 0 = 0 := by
  have h0 := h 0 P.base
  rw [P.ind3_zero] at h0
  linarith

/-- The shift is additive; uses `ind3_add` and a cancellation in `Real`. -/
theorem volumeTranslationLaw_shift_add
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (shift : Nat → Real)
    (h : ∀ (m : Nat) (c : Choice),
      Q.logVolume (P.ind3 m c) = Q.logVolume c + shift m)
    (m n : Nat) :
    shift (m + n) = shift m + shift n := by
  have h1 := h (m + n) P.base
  rw [P.ind3_add] at h1
  have h2 := h n (P.ind3 m P.base)
  have h3 := h m P.base
  linarith

/-- The shift is nonnegative; uses the packet upper-semi law `ind3_volume`. -/
theorem volumeTranslationLaw_shift_nonneg
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (shift : Nat → Real)
    (h : ∀ (m : Nat) (c : Choice),
      Q.logVolume (P.ind3 m c) = Q.logVolume c + shift m)
    (m : Nat) :
    0 ≤ shift m := by
  have h1 := h m P.base
  have h2 := Q.ind3_volume m P.base
  linarith

/-- The shift is monotone. -/
theorem volumeTranslationLaw_shift_monotone
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (shift : Nat → Real)
    (h : ∀ (m : Nat) (c : Choice),
      Q.logVolume (P.ind3 m c) = Q.logVolume c + shift m)
    {m n : Nat} (hmn : m ≤ n) :
    shift m ≤ shift n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [volumeTranslationLaw_shift_add P Q shift h m k]
  have hnn := volumeTranslationLaw_shift_nonneg P Q shift h k
  linarith

end

end K1K2Realization

/-! ## 5. Instance on the concrete finite model -/

namespace ConcreteFiniteTheorem311

/-- The concrete finite model satisfies the volume-translation law with shift
`m |-> m`: reuse of `normalizedLogVolume_ind3Lift_add`. -/
theorem normalizedLogVolume_volumeTranslationData (l : PrimeGeFive) :
    K1K2Realization.VolumeTranslationData (normalizedLogVolume l)
      (fun m c => ProcessionChoice.ind3Lift m c) :=
  ⟨fun m => (m : Real), fun m c => normalizedLogVolume_ind3Lift_add l m c⟩

end ConcreteFiniteTheorem311

end LeanFormal.IUT

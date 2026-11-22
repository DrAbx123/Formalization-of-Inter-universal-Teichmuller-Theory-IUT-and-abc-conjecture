import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2VolumeTranslationLaw
import Mathlib.Tactic

/-!
  # Ind3 direction audit and log-scaling probe (forwarded candidates T10/T5)
  (run k1k2-realization-20261016, continuation package)

  T10 (Ind3 direction audit): the packet's upper-semi law is the weak
  inequality `logVolume c <= logVolume (ind3 m c)` (`ind3_volume` of the
  packet; `logVolume_ind3_upper` on the K1 record).  The volume-translation
  law is conditional data (`VolumeTranslationData`); it does not follow from
  the weak law, and the weak law's direction is the only unconditional
  direction.  This file records two direction guards:

  * `logVolume_ind3_strict_of_shift_pos`: a strictly positive translation
    shift forces strict increase (`<`), so the weak `<=` is the correct
    direction and cannot be upgraded to an equality under the translation
    law.
  * `normalizedLogVolume_ind3Lift_strict` (finite model): the increase is
    strict for every positive level; the model's volume is `vol + n` with
    `n > 0`, consistent with the weak direction and incompatible with
    "equality at all levels".

  T5 (hclass homogeneity): the log-scaling law `logVol (lambda . c) =
  logVol c + r * log lambda`, in its discrete (Nat-indexed) shadow:

  * `VolumeLogScalingLaw`: the law at the level of a volume datum plus a
    Nat-indexed action;
  * `volumeLogScalingLaw_unique`: the exponent is unique once `log 2 != 0`;
  * `additiveShift_logScaling_iff_zero`: a Nat-additive shift is log-scaled
    (for some `r`) if and only if it vanishes identically -- via
    `volumeTranslationLaw_shift_add` this says the frozen translation law can
    be log-homogeneous only with zero shift;
  * `normalizedLogVolume_no_uniform_logScaling` (finite model): the concrete
    model's shift `n |-> n` admits no uniform log-scaling exponent; witness
    levels `2` and `8 = 2 ^ 3` force `6 = 8`.

  Status boundary: these are discrete-shadow statements.  The continuous
  positive-real action on `ProcessionChoice` by scaling is not modeled by the
  frozen interfaces and is not constructed here; the real-lambda homogeneity
  law for the source log-shells remains a source obligation.
-/

set_option linter.unusedVariables false

namespace LeanFormal.IUT

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## T10: Ind3 direction guards -/

/-- T10 direction guard: under the volume-translation law, a strictly positive
shift at level `m` yields strict increase of the log-volume; the weak packet
inequality `ind3_volume` records the correct (non-strict) direction. -/
theorem logVolume_ind3_strict_of_shift_pos
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (shift : Nat → Real)
    (h : ∀ (m : Nat) (c : Choice),
      Q.logVolume (P.ind3 m c) = Q.logVolume c + shift m)
    {m : Nat} (hm : 0 < shift m) (c : Choice) :
    Q.logVolume c < Q.logVolume (P.ind3 m c) := by
  rw [h m c]
  linarith

/-! ## T5: discrete log-scaling law -/

/-- The discrete log-scaling law: the `n`-th level of a Nat-indexed action
adds `r * log n` to the volume.  This is the Nat-indexed shadow of the
real-lambda homogeneity law `logVol (lambda . c) = logVol c + r * log lambda`. -/
def VolumeLogScalingLaw {ι : Type*} (volume : ι → Real) (act : Nat → ι → ι)
    (r : Real) : Prop :=
  ∀ (n : Nat) (c : ι), volume (act n c) = volume c + r * Real.log n

/-- T5 uniqueness: a log-scaling exponent is unique once some level has
nonzero logarithm (`n = 2`). -/
theorem volumeLogScalingLaw_unique {ι : Type*} (volume : ι → Real)
    (act : Nat → ι → ι) {r r' : Real}
    (hr : VolumeLogScalingLaw volume act r)
    (hr' : VolumeLogScalingLaw volume act r') (c : ι) : r = r' := by
  have hcomp : volume c + r * Real.log ((2 : Nat) : Real) =
      volume c + r' * Real.log ((2 : Nat) : Real) := by
    rw [← hr 2 c, ← hr' 2 c]
  have hmul : r * Real.log ((2 : Nat) : Real) =
      r' * Real.log ((2 : Nat) : Real) :=
    add_left_cancel hcomp
  exact mul_right_cancel₀
    (ne_of_gt (Real.log_pos (by norm_num : (1 : Real) < ((2 : Nat) : Real))))
    hmul

/-- T5 criterion: a Nat-additive shift is expressible as `r * log n` for some
exponent if and only if it vanishes identically.  (The shift of the
volume-translation law is Nat-additive by `volumeTranslationLaw_shift_add`,
with `shift 0 = 0` by `volumeTranslationLaw_shift_zero`.) -/
theorem additiveShift_logScaling_iff_zero (shift : Nat → Real)
    (hadd : ∀ m n : Nat, shift (m + n) = shift m + shift n)
    (h0 : shift 0 = 0) :
    (∃ r : Real, ∀ n : Nat, shift n = r * Real.log n) ↔
      ∀ n : Nat, shift n = 0 := by
  constructor
  · rintro ⟨r, hr⟩ n
    induction n with
    | zero => exact h0
    | succ k ih =>
      rw [← Nat.succ_eq_add_one k, hadd k 1, ih, hr 1]
      simp
  · intro hzero
    exact ⟨0, fun n => by rw [hzero n, zero_mul]⟩

end

end K1K2Realization

/-! ## Finite-model instances -/

namespace ConcreteFiniteTheorem311

/-- T10 finite model: the volume increase along `ind3Lift n` is strict for
every positive level; the model satisfies the `vol + n` law as a strict
inequality. -/
theorem normalizedLogVolume_ind3Lift_strict (l : PrimeGeFive) {n : Nat}
    (hn : 1 ≤ n) (c : ProcessionChoice l) :
    normalizedLogVolume l c <
      normalizedLogVolume l (ProcessionChoice.ind3Lift n c) := by
  rw [normalizedLogVolume_ind3Lift_add]
  have hn' : (0 : Real) < (n : Real) := by exact_mod_cast hn
  linarith

/-- T5 finite-model separation: the concrete model's power action
`n |-> ind3Lift n` admits no uniform log-scaling exponent.  The increase is
the multiplicative exponent `n` (translation shift `n |-> n`), not `log n`:
levels `2` and `8 = 2 ^ 3` would force `r log 2 = 2` and `3 (r log 2) = 8`,
hence `6 = 8`. -/
theorem normalizedLogVolume_no_uniform_logScaling (l : PrimeGeFive) :
    ¬ ∃ r : Real, ∀ (n : Nat) (c : ProcessionChoice l),
      normalizedLogVolume l (ProcessionChoice.ind3Lift n c) =
        normalizedLogVolume l c + r * Real.log n := by
  rintro ⟨r, hr⟩
  have h2 := hr 2 ProcessionChoice.base
  have h8 := hr 8 ProcessionChoice.base
  rw [normalizedLogVolume_ind3Lift_add] at h2
  rw [normalizedLogVolume_ind3Lift_add] at h8
  have h2' : r * Real.log ((2 : Nat) : Real) = ((2 : Nat) : Real) :=
    (add_left_cancel h2).symm
  have h8' : r * Real.log ((8 : Nat) : Real) = ((8 : Nat) : Real) :=
    (add_left_cancel h8).symm
  have hlog8 : Real.log ((8 : Nat) : Real) =
      3 * Real.log ((2 : Nat) : Real) := by
    have hpow : ((8 : Nat) : Real) = ((2 : Nat) : Real) ^ 3 := by norm_num
    rw [hpow, Real.log_pow]
    norm_num
  have h8'' : 3 * (r * Real.log ((2 : Nat) : Real)) = ((8 : Nat) : Real) := by
    calc 3 * (r * Real.log ((2 : Nat) : Real))
        = r * (3 * Real.log ((2 : Nat) : Real)) := by ring
      _ = r * Real.log ((8 : Nat) : Real) := by rw [hlog8]
      _ = ((8 : Nat) : Real) := h8'
  have h6 : 3 * (r * Real.log ((2 : Nat) : Real)) = ((6 : Nat) : Real) := by
    rw [h2']
    norm_num
  have hcontra : ((6 : Nat) : Real) = ((8 : Nat) : Real) := by
    rw [← h6, ← h8'']
  norm_num at hcontra

end ConcreteFiniteTheorem311

end LeanFormal.IUT

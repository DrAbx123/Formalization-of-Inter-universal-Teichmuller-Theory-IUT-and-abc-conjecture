import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

namespace ABCBridge.LogShellFrobeniusConsumerGeneral

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NumberField

variable {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]
variable (place : FinitePlaceAtPrime F p)

/-- The actual normalized completion at the common prime. -/
abbrev ConsumerField (place : FinitePlaceAtPrime F p) : Type := CommonPrimeCompletion place

/-- The actual principal-unit log-shell image at the common prime. -/
abbrev ConsumerLogShell (place : FinitePlaceAtPrime F p) : AddSubgroup (ConsumerField place) :=
  principalUnitLogImage (K := ConsumerField place) p

/-- p-fold scaling on the actual principal-unit log-shell image, induced by
the p-power Frobenius `u |-> u^p` through the actual logarithm. -/
noncomputable def consumerLogShellFrobenius :
    ConsumerLogShell place →+ ConsumerLogShell place where
  toFun x :=
    ⟨(p : ConsumerField place) * (x : ConsumerField place), by
      rcases x.property with ⟨u, hu⟩
      refine ⟨u ^ p, ?_⟩
      rw [← hu]
      exact principalUnitLog_pow (K := ConsumerField place) p p u⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]

@[simp] theorem consumerLogShellFrobenius_apply
    (x : ConsumerLogShell place) :
    (consumerLogShellFrobenius place x : ConsumerField place) =
      (p : ConsumerField place) * (x : ConsumerField place) := rfl

/-- Iterated consumer action on the actual principal-unit log-shell image. -/
theorem consumerLogShellFrobenius_iterate_apply
    (x : ConsumerLogShell place) (n : ℕ) :
    (((consumerLogShellFrobenius place)^[n]) x : ConsumerField place) =
      (p : ConsumerField place) ^ n * (x : ConsumerField place) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', consumerLogShellFrobenius_apply]
      simp only [ih]
      calc
        (p : ConsumerField place) *
            ((p : ConsumerField place) ^ n * (x : ConsumerField place)) =
          ((p : ConsumerField place) ^ n * (p : ConsumerField place)) *
              (x : ConsumerField place) := by ring
        _ = (p : ConsumerField place) ^ (n + 1) *
              (x : ConsumerField place) :=
          congrArg (fun y => y * (x : ConsumerField place))
            (pow_succ (p : ConsumerField place) n).symm

/-- Consumer interface at the actual normalized completion: forall `n`, the
`n`-fold p-power Frobenius is `p^n`-fold scaling on the principal-unit
log-shell image. -/
theorem frobeniusConsumerGeneral_apply
    (n : ℕ) (x : ConsumerLogShell place) :
    (((consumerLogShellFrobenius place)^[n]) x : ConsumerField place) =
      (p : ConsumerField place) ^ n * (x : ConsumerField place) :=
  consumerLogShellFrobenius_iterate_apply place x n

theorem frobeniusConsumerGeneral_apply_nsmul
    (n : ℕ) (x : ConsumerLogShell place) :
    (((consumerLogShellFrobenius place)^[n]) x : ConsumerField place) =
      (p ^ n : ℕ) • (x : ConsumerField place) := by
  rw [frobeniusConsumerGeneral_apply, nsmul_eq_mul, Nat.cast_pow]

/-- Exact prime exposure: the common prime of the actual place is `p`. -/
theorem completionRationalPrime_exposure :
    (completionRationalPrime place.val).val = p := place.property

/-- Exact paper-scale exposure: `logShellScale p` is `p` for odd `p` and
`p^2` only at `p = 2`. -/
theorem logShellScale_exposure :
    logShellScale p = if p = 2 then p ^ 2 else p := by
  unfold logShellScale
  split_ifs <;> rfl

/-- At an odd common prime the consumer action is exactly the paper
`logShellScale p`-fold scaling. -/
theorem frobeniusConsumerGeneral_apply_logShellScale_of_odd
    (h : p ≠ 2) (n : ℕ) (x : ConsumerLogShell place) :
    (((consumerLogShellFrobenius place)^[n]) x : ConsumerField place) =
      (logShellScale p : ConsumerField place) ^ n *
        (x : ConsumerField place) := by
  rw [frobeniusConsumerGeneral_apply]
  have hs : logShellScale p = p := by simp [logShellScale, h]
  rw [hs]

end

end ABCBridge.LogShellFrobeniusConsumerGeneral

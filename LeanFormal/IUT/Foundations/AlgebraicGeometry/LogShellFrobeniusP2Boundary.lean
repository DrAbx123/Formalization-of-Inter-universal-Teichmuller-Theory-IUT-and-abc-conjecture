import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellFrobeniusConsumerGeneral
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# p = 2 boundary of the log-shell Frobenius consumer

The actual p-power Frobenius on principal units is always `u |-> u^p`, hence
its log-shell action is p-fold scaling for every prime p.  At p = 2 the paper
scale is `logShellScale 2 = 4`, so the actual 2-fold action is NOT the
paper 4-fold scaling.  This file records that exact non-identification; no
unconditional equality is asserted.

Actual consumers audited:
* `ABCBridge.LogShellFrobeniusConsumerGeneral.frobeniusConsumerGeneral_apply`
  (general p-fold action; valid at p = 2 as 2-fold, not 4-fold).
* `ABCBridge.LogShellFrobeniusConsumerGeneral.frobeniusConsumerGeneral_apply_logShellScale_of_odd`
  (paper-scale identification only for p != 2; excludes p = 2).
* `ABCBridge.LogShellFrobeniusConsumer.frobeniusPowerConsumer_apply`
  (concrete Q5/p=5 model; not a p=2 consumer).
* `ABCBridge.LogShellFrobeniusPower.principalUnitLogShellFrobenius_iterate_apply`
  (concrete Q5/p=5 model; not a p=2 consumer).
-/

namespace ABCBridge.LogShellFrobeniusP2Boundary

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open ABCBridge.LogShellFrobeniusConsumerGeneral

/-- The paper scale at p = 2 is exactly four. -/
theorem logShellScale_two : logShellScale 2 = 4 := by
  norm_num [logShellScale]

/-- In characteristic zero, 2 is not 4. -/
theorem two_ne_four {K : Type*} [Field K] [CharZero K] : (2 : K) ≠ 4 := by
  norm_num

section PTwoBoundary

variable {F : Type} [Field F] [NumberField F]
variable (place : FinitePlaceAtPrime F 2)

/-- At p = 2 the actual consumer action is exactly 2-fold scaling (the
p-power Frobenius), not the paper 4-fold scale. -/
theorem pTwo_consumerLogShellFrobenius_apply
    (x : ConsumerLogShell place) :
    (consumerLogShellFrobenius place x : ConsumerField place) =
      (2 : ConsumerField place) * (x : ConsumerField place) := by
  simpa using consumerLogShellFrobenius_apply place x

/-- The actual 2-fold action is not 4-fold scaling on any nonzero log-shell
element.  This is the exact p = 2 non-identification. -/
theorem pTwo_consumerLogShellFrobenius_ne_fourfold
    (x : ConsumerLogShell place) (hx : (x : ConsumerField place) ≠ 0) :
    (consumerLogShellFrobenius place x : ConsumerField place) ≠
      (4 : ConsumerField place) * (x : ConsumerField place) := by
  rw [pTwo_consumerLogShellFrobenius_apply]
  intro h
  have h24 : (2 : ConsumerField place) = 4 := mul_right_cancel₀ hx h
  exact two_ne_four h24

/-- The same non-identification expressed with the paper scale: the actual
p=2 action is not `logShellScale 2`-fold scaling. -/
theorem pTwo_consumerLogShellFrobenius_ne_logShellScale_fold
    (x : ConsumerLogShell place) (hx : (x : ConsumerField place) ≠ 0) :
    (consumerLogShellFrobenius place x : ConsumerField place) ≠
      (logShellScale 2 : ConsumerField place) * (x : ConsumerField place) := by
  rw [logShellScale_two]
  exact pTwo_consumerLogShellFrobenius_ne_fourfold place x hx

end PTwoBoundary

end

end ABCBridge.LogShellFrobeniusP2Boundary

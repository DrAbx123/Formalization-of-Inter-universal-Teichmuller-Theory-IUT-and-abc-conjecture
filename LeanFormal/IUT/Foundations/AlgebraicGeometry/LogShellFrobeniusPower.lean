import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellFrobeniusAction
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace ABCBridge.LogShellFrobeniusPower

noncomputable section

open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellFrobeniusAction
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

local instance logShellFrobeniusPowerFivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The p-power Frobenius on the full actual local unit group. -/
noncomputable def localUnitFrobenius :
    (Integers concreteLogShellField)ˣ →* (Integers concreteLogShellField)ˣ where
  toFun u := u ^ concreteRationalPrime
  map_one' := one_pow _
  map_mul' u v := mul_pow u v _

@[simp] theorem localUnitFrobenius_apply
    (u : (Integers concreteLogShellField)ˣ) :
    localUnitFrobenius u = u ^ concreteRationalPrime := rfl

theorem localUnitFrobenius_iterate
    (u : (Integers concreteLogShellField)ˣ) (n : ℕ) :
    (localUnitFrobenius^[n]) u = u ^ (concreteRationalPrime ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, localUnitFrobenius_apply, ← pow_mul]
      rfl

/-- The actual p-adic logarithm of the p-power Frobenius is p times the
logarithm, on the principal units of the actual completion. -/
theorem localUnitFrobenius_log
    (u : (Integers concreteLogShellField)ˣ) (hu : u ∈ principalUnits) :
    unitLog (K := concreteLogShellField) (localUnitFrobenius u) =
      (concreteRationalPrime : concreteLogShellField) *
        unitLog (K := concreteLogShellField) u := by
  simpa [localUnitFrobenius, principalUnitFrobenius] using
    unitLog_principalUnitFrobenius_log ⟨u, hu⟩

/-- Iterated logarithm scaling: the `n`-fold p-power Frobenius multiplies the
logarithm by `p^n`. -/
theorem localUnitFrobenius_iterate_log
    (u : (Integers concreteLogShellField)ˣ) (n : ℕ) :
    unitLog (K := concreteLogShellField) ((localUnitFrobenius^[n]) u) =
      (concreteRationalPrime : concreteLogShellField) ^ n *
        unitLog (K := concreteLogShellField) u := by
  rw [localUnitFrobenius_iterate, unitLog_pow
    (p := concreteRationalPrime) (K := concreteLogShellField)]
  push_cast
  ring

/-- Iterated p-fold scaling on the principal-unit log-shell image. -/
theorem principalUnitLogShellFrobenius_iterate_apply
    (x : principalUnitLogShell) (n : ℕ) :
    ((principalUnitLogShellFrobenius^[n]) x : concreteLogShellField) =
      (concreteRationalPrime : concreteLogShellField) ^ n *
        (x : concreteLogShellField) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', principalUnitLogShellFrobenius_apply]
      simp only [ih]
      calc
        (concreteRationalPrime : concreteLogShellField) *
            ((concreteRationalPrime : concreteLogShellField) ^ n *
              (x : concreteLogShellField)) =
          ((concreteRationalPrime : concreteLogShellField) ^ n *
            (concreteRationalPrime : concreteLogShellField)) *
              (x : concreteLogShellField) := by ring
        _ = (concreteRationalPrime : concreteLogShellField) ^ (n + 1) *
              (x : concreteLogShellField) :=
          congrArg (fun y => y * (x : concreteLogShellField))
            (pow_succ (concreteRationalPrime : concreteLogShellField) n).symm


end

end ABCBridge.LogShellFrobeniusPower

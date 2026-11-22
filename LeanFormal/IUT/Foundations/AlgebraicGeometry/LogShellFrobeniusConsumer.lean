import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellFrobeniusPower
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace ABCBridge.LogShellFrobeniusConsumer

noncomputable section

open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellFrobeniusAction
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

/-- The actual normalized completion at which the Frobenius consumer is stated. -/
abbrev actualNormalizedCompletion : Type := concreteLogShellField

/-- Consumer interface: the `n`-fold p-power Frobenius acts on the actual
principal-unit log-shell image as the `n`-fold p-fold scaling. -/
theorem frobeniusPowerConsumer_apply
    (n : ℕ) (x : principalUnitLogShell) :
    ((principalUnitLogShellFrobenius^[n]) x : actualNormalizedCompletion) =
      (concreteRationalPrime : actualNormalizedCompletion) ^ n *
        (x : actualNormalizedCompletion) :=
  LogShellFrobeniusPower.principalUnitLogShellFrobenius_iterate_apply x n

/-- The same consumer identity in `nsmul` form: `(F^[n]) x = p^n • x`. -/
theorem frobeniusPowerConsumer_apply_nsmul
    (n : ℕ) (x : principalUnitLogShell) :
    ((principalUnitLogShellFrobenius^[n]) x : actualNormalizedCompletion) =
      (concreteRationalPrime ^ n : ℕ) • (x : actualNormalizedCompletion) := by
  rw [frobeniusPowerConsumer_apply, nsmul_eq_mul, Nat.cast_pow]


/-- Exact scale exposure: away from p = 2, the paper log-shell scale is the
prime itself.  At the concrete odd place this is the intended p-scaling. -/
theorem logShellScale_eq_prime_of_ne_two
    (h : concreteRationalPrime ≠ 2) :
    logShellScale concreteRationalPrime = concreteRationalPrime := by
  simp [logShellScale, h]

/-- Scale-exact consumer form: when the actual prime is odd, the same action
is `logShellScale p`-fold, exposing the paper scale rather than only `p`. -/
theorem frobeniusPowerConsumer_apply_logShellScale
    (h : concreteRationalPrime ≠ 2) (n : ℕ) (x : principalUnitLogShell) :
    ((principalUnitLogShellFrobenius^[n]) x : actualNormalizedCompletion) =
      (logShellScale concreteRationalPrime : actualNormalizedCompletion) ^ n *
        (x : actualNormalizedCompletion) := by
  rw [frobeniusPowerConsumer_apply, logShellScale_eq_prime_of_ne_two h]

end

end ABCBridge.LogShellFrobeniusConsumer

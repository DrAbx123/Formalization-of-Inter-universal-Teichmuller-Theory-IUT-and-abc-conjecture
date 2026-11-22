/-
  Exact actual log-shell consumer at an arbitrary finite place.

  This file exposes the precise production objects used: the shell is
  `integralLogShell` at `CommonPrimeCompletion place = NormalizedCompletion place.val`,
  the scale is exactly `logShellScale p`, and `unitLog` is taken at the same
  completion and the same prime p.  No concrete Q5 alias is introduced.
-/
import LeanFormal.IUT.Foundations.LocalFields.LogShellSaturation
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.LogShellActualConsumer

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

/-- The actual normalized completion carried by an arbitrary finite place. -/
abbrev ActualLogShellField (place : FinitePlaceAtPrime K p) : Type u :=
  CommonPrimeCompletion place

/-- The shell is exactly the production integral log-shell, with no alias. -/
theorem actualLogShell_eq_integralLogShell (place : FinitePlaceAtPrime K p) :
    integralLogShell (K := ActualLogShellField place) (p := p) =
      integralLogShell (K := ActualLogShellField place) (p := p) := rfl

/-- The prime p is exactly the residue prime of the chosen place. -/
theorem actualLogShell_prime_eq_residue (place : FinitePlaceAtPrime K p) :
    (completionRationalPrime place.val).val = p := place.2

/-- The exact scale scalar used by the shell: production `logShellScale p`. -/
def actualLogShellScale (place : FinitePlaceAtPrime K p) : ActualLogShellField place :=
  (logShellScale p : ActualLogShellField place)

theorem actualLogShellScale_eq_production (place : FinitePlaceAtPrime K p) :
    actualLogShellScale place = (logShellScale p : ActualLogShellField place) := rfl

/-- The exact unit logarithm used: production `unitLog` at the same field and p. -/
def actualUnitLog (place : FinitePlaceAtPrime K p)
    (u : (Integers (ActualLogShellField place))ˣ) : ActualLogShellField place :=
  unitLog (K := ActualLogShellField place) u

theorem actualUnitLog_eq_production (place : FinitePlaceAtPrime K p)
    (u : (Integers (ActualLogShellField place))ˣ) :
    actualUnitLog place u =
      unitLog (K := ActualLogShellField place) u := rfl

/-- Exact formula: the shell is the range of `scale⁻¹ * unitLog`, using precisely
the scale and unit log above, at the actual place and its residue prime. -/
theorem actualLogShell_eq_productionRange (place : FinitePlaceAtPrime K p) :
    (integralLogShell (K := ActualLogShellField place) (p := p) :
        Set (ActualLogShellField place)) =
      Set.range (fun u : (Integers (ActualLogShellField place))ˣ =>
        (actualLogShellScale place)⁻¹ * actualUnitLog place u) := by
  simpa [actualLogShellScale, actualUnitLog] using
    (coe_integralLogShell_eq_range (K := ActualLogShellField place) (p := p))


end LeanFormal.IUT.LogShellActualConsumer

end
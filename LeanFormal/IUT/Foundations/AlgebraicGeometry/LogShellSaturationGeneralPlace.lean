/-
  Log-shell saturation at an arbitrary finite place over a common prime p.

  The place is a `FinitePlaceAtPrime K p`; its actual completion is
  `CommonPrimeCompletion place = NormalizedCompletion place.val`.  The production
  `LogShellSaturation` statement is instantiated without duplicating any shell
  infrastructure.
-/
import LeanFormal.IUT.Foundations.LocalFields.LogShellSaturation
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.LogShellSaturationGeneralPlace

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

/-- The actual normalized completion at an arbitrary finite place over p. -/
abbrev ActualCommonPrimeLocalField (place : FinitePlaceAtPrime K p) : Type u :=
  CommonPrimeCompletion place

/-- The actual integral log-shell at that place, with the common prime p. -/
abbrev commonPrimeIntegralLogShell (place : FinitePlaceAtPrime K p) :
    Set (ActualCommonPrimeLocalField place) :=
  integralLogShell (K := ActualCommonPrimeLocalField place) (p := p)

/-- Saturation consumer at an arbitrary finite place: every element of the actual
integral log-shell is the normalized logarithm of an integral unit. -/
theorem commonPrimeLogShell_saturation (place : FinitePlaceAtPrime K p)
    (y : ActualCommonPrimeLocalField place) :
    y ∈ commonPrimeIntegralLogShell place ↔
      ∃ u : (Integers (ActualCommonPrimeLocalField place))ˣ,
        (logShellScale p : ActualCommonPrimeLocalField place)⁻¹ * unitLog u = y := by
  rw [commonPrimeIntegralLogShell, coe_integralLogShell_eq_range]
  rfl

/-- Surjective form of the general-place saturation consumer. -/
theorem commonPrimeLogShell_exists_integralUnit (place : FinitePlaceAtPrime K p)
    {y : ActualCommonPrimeLocalField place} (hy : y ∈ commonPrimeIntegralLogShell place) :
    ∃ u : (Integers (ActualCommonPrimeLocalField place))ˣ,
      (logShellScale p : ActualCommonPrimeLocalField place)⁻¹ * unitLog u = y :=
  (commonPrimeLogShell_saturation place y).mp hy

/-- Integral-unit generation at an arbitrary finite place: every integral unit is
a p-power iterate times a unit modulo the torsion kernel. -/
theorem commonPrimeIntegralUnit_generation (place : FinitePlaceAtPrime K p)
    (u : (Integers (ActualCommonPrimeLocalField place))ˣ) :
    ∃ (n : ℕ) (w : (Integers (ActualCommonPrimeLocalField place))ˣ),
      unitLog u = ((((p : ℕ) ^ n : ℕ) : ActualCommonPrimeLocalField place) * unitLog w) ∧
        IsOfFinOrder (u * (w ^ ((p : ℕ) ^ n))⁻¹) :=
  integralLogShell_unitLog_generation (K := ActualCommonPrimeLocalField place)
    (p := p) u

end LeanFormal.IUT.LogShellSaturationGeneralPlace

end

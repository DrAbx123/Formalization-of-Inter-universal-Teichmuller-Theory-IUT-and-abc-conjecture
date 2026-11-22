/-
  Consumer of production LogShellSaturation at the actual local field K_v.

  K_v is the normalized completion of a number field at a finite place v, with
  its actual residue prime p.  The production log-shell saturation theorems are
  instantiated here; no local-field or log-shell infrastructure is duplicated.
-/
import LeanFormal.IUT.Foundations.LocalFields.LogShellSaturation
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.LogShellSaturationConsumer

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The actual local field at the finite place v. -/
abbrev ActualLocalField (v : NumberField.FinitePlace K) : Type u :=
  NormalizedCompletion v

/-- The actual residue prime p_v underneath v. -/
abbrev actualLocalPrime (v : NumberField.FinitePlace K) : ℕ :=
  (completionRationalPrime v).val

instance actualLocalPrimeFact (v : NumberField.FinitePlace K) :
    Fact (actualLocalPrime v).Prime :=
  completionRationalPrime_fact v

/-- The actual integral log-shell at v. -/
abbrev actualIntegralLogShell (v : NumberField.FinitePlace K) : Set (ActualLocalField v) :=
  integralLogShell (K := ActualLocalField v) (p := actualLocalPrime v)

/-- Saturation consumer: every element of the actual integral log-shell is the
normalized logarithm of an integral unit.  This is production part (c),
instantiated at the actual local field. -/
theorem actualLocalLogShell_saturation (v : NumberField.FinitePlace K)
    (y : ActualLocalField v) :
    y ∈ actualIntegralLogShell v ↔
      ∃ u : (Integers (ActualLocalField v))ˣ,
        (logShellScale (actualLocalPrime v) : ActualLocalField v)⁻¹ * unitLog u = y := by
  rw [actualIntegralLogShell, coe_integralLogShell_eq_range]
  rfl

/-- Surjective form of the same saturation consumer. -/
theorem actualLocalLogShell_exists_integralUnit (v : NumberField.FinitePlace K)
    {y : ActualLocalField v} (hy : y ∈ actualIntegralLogShell v) :
    ∃ u : (Integers (ActualLocalField v))ˣ,
      (logShellScale (actualLocalPrime v) : ActualLocalField v)⁻¹ * unitLog u = y :=
  (actualLocalLogShell_saturation v y).mp hy

/-- Integral-unit generation at the actual local field: every integral unit is
a p-power iterate times a unit modulo the torsion kernel. -/
theorem actualLocalIntegralUnit_generation (v : NumberField.FinitePlace K)
    (u : (Integers (ActualLocalField v))ˣ) :
    ∃ (n : ℕ) (w : (Integers (ActualLocalField v))ˣ),
      unitLog u = ((((actualLocalPrime v : ℕ) ^ n : ℕ) : ActualLocalField v) * unitLog w) ∧
        IsOfFinOrder (u * (w ^ ((actualLocalPrime v : ℕ) ^ n))⁻¹) :=
  integralLogShell_unitLog_generation (K := ActualLocalField v)
    (p := actualLocalPrime v) u

end LeanFormal.IUT.LogShellSaturationConsumer

end
import LeanFormal.IUT.Foundations.LocalFields.LogShellSaturation
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Log-shell localization consumer at the actual finite place

This file instantiates the tensor/base-change compatibility for the integral
log-shell lattice and the production log-shell saturation theorem at the
actual local field K_v of a number field at a finite place v.

The actual residue prime is p_v = completionRationalPrime v; no raw numeric
prime or Q5 alias is used.  The tensor statement is the Q_p-base-change
finrank compatibility of L0.4.
-/

open scoped TensorProduct

noncomputable section

namespace LeanFormal.IUT.LogShellLocalizationConsumer

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

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

/-- Restrict the Q_p-algebra structure of K_v to Z_p. -/
noncomputable instance actualLocalFieldAlgebra (v : NumberField.FinitePlace K) :
    Algebra ℤ_[actualLocalPrime v] (ActualLocalField v) :=
  Algebra.restrictScalars ℤ_[actualLocalPrime v] ℚ_[actualLocalPrime v]
    (ActualLocalField v)

instance actualLocalFieldModule (v : NumberField.FinitePlace K) :
    Module ℤ_[actualLocalPrime v] (ActualLocalField v) :=
  Algebra.toModule

/-- The actual integral log-shell lattice at v. -/
abbrev actualIntegralLogShellLattice (v : NumberField.FinitePlace K) :
    Submodule ℤ_[actualLocalPrime v] (ActualLocalField v) :=
  integralLogShellLattice (K := ActualLocalField v) (p := actualLocalPrime v)

/-- The actual integral log-shell at v. -/
abbrev actualIntegralLogShell (v : NumberField.FinitePlace K) : Set (ActualLocalField v) :=
  integralLogShell (K := ActualLocalField v) (p := actualLocalPrime v)

/-- Saturation of the actual integral log-shell at v (production part (c)). -/
theorem actualLocalLogShell_saturation (v : NumberField.FinitePlace K)
    (y : ActualLocalField v) :
    y ∈ actualIntegralLogShell v ↔
      ∃ u : (Integers (ActualLocalField v))ˣ,
        (logShellScale (actualLocalPrime v) : ActualLocalField v)⁻¹ * unitLog u = y := by
  rw [actualIntegralLogShell, coe_integralLogShell_eq_range]
  rfl

/-- Tensor/base-change compatibility of the actual integral log-shell lattice:
after base change to Q_{p_v}, its finrank equals the local field degree. -/
theorem actualIntegralLogShellLattice_tensor_baseChange_finrank
    (v : NumberField.FinitePlace K) :
    Module.finrank ℚ_[actualLocalPrime v]
        (TensorProduct ℤ_[actualLocalPrime v] ℚ_[actualLocalPrime v]
          (actualIntegralLogShellLattice v)) =
      Module.finrank ℚ_[actualLocalPrime v] (ActualLocalField v) := by
  rw [Module.finrank_baseChange]
  exact finrank_integralLogShellLattice (K := ActualLocalField v)
    (p := actualLocalPrime v)

end LeanFormal.IUT.LogShellLocalizationConsumer

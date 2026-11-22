import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Tensor/localization compatibility for log-shell lattices

This file records two compatibility facts used by the localization-span route:

* base change to an away localization R_e is the away localization of A at
  algebraMap R A e (IsLocalization.Away.tensorRight);
* the integral logarithmic shell lattice of a finite extension is finite free
  over Z_p, so its tensor base change to Q_p has the same finrank as the
  field.  The production log-shell finrank theorem is consumed directly.
-/

open scoped TensorProduct

noncomputable section

namespace LeanFormal.IUT.LogTensorLocalizationCompat

universe u

section AwayTensor

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Base change of A to the away localization R_e is the away localization
of A at the image of e. -/
theorem tensorProduct_away_isLocalization (e : R) :
    IsLocalization.Away (algebraMap R A e)
      (TensorProduct R (Localization.Away e) A) :=
  IsLocalization.Away.tensorRight (S := A) e (Localization.Away e)

end AwayTensor

section LogShell

open LeanFormal.IUT.LocalFieldLogarithm

variable {K : Type u} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] {p : ℕ} [Fact p.Prime]
  [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- Tensor base change to Q_p of the actual integral log-shell lattice has
the same Q_p-dimension as the local field. -/
theorem integralLogShellLattice_tensor_baseChange_finrank :
    Module.finrank ℚ_[p]
        (TensorProduct ℤ_[p] ℚ_[p]
          (integralLogShellLattice (K := K) (p := p))) =
      Module.finrank ℚ_[p] K := by
  rw [Module.finrank_baseChange]
  exact finrank_integralLogShellLattice (K := K) (p := p)

end LogShell

end LeanFormal.IUT.LogTensorLocalizationCompat

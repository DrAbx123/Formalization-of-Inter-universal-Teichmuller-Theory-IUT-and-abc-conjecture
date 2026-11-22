
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace

namespace S2223Probe

universe u

variable {F : Type u} [Field F] [NumberField F]

abbrev L (place : NumberField.FinitePlace F) := Completion place
abbrev Lbar (place : NumberField.FinitePlace F) := AlgebraicClosure (Completion place)

noncomputable def qUnit (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) : (Lbar place)ˣ :=
  tateParameterUnit place parameter.q parameter.q_ne_zero

theorem qUnit_zpow_eq_one_iff (place : NumberField.FinitePlace F)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place) (m : ℤ) :
    qUnit place parameter ^ m = 1 ↔ m = 0 := by
  constructor
  · intro hm
    have hm' : (((qUnit place parameter) ^ m : (Lbar place)ˣ) : Lbar place) = 1 := by
      rw [hm]; rfl
    have hval : algebraMap (L place) (Lbar place) (parameter.q ^ m) = 1 := by
      simpa [qUnit, NumberFieldFinitePlace.tateParameterUnit, Units.val_pow_eq_pow_val] using hm'
    have hq : parameter.q ^ m = 1 := by
      apply (algebraMap (L place) (Lbar place)).injective
      simpa using hval
    have hnorm : ‖parameter.q‖ ^ m = 1 := by
      calc ‖parameter.q‖ ^ m = ‖parameter.q ^ m‖ := (norm_zpow _ _).symm
        _ = ‖(1 : L place)‖ := by rw [hq]
        _ = 1 := by simp
    have hpos : 0 < ‖parameter.q‖ := norm_pos_iff.mpr parameter.q_ne_zero
    have hne : ‖parameter.q‖ ≠ 1 := by
      intro h
      have hlt : ‖parameter.q‖ < 1 := by
        rw [Valued.toNormedField.norm_lt_one_iff]
        exact parameter.valuation_lt_one
      rw [h] at hlt
      exact lt_irrefl 1 hlt
    exact (zpow_eq_one_iff_right₀ hpos.le hne).mp hnorm
  · intro hm
    rw [hm, zpow_zero]

end S2223Probe
end

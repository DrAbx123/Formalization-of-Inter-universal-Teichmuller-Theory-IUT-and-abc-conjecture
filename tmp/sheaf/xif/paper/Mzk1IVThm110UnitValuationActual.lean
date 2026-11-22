import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitValuationActual
variable {p : Nat} [Fact p.Prime]
/-- A Zp-unit has Qp-valuation 0. -/
theorem zpUnit_valuation_eq_zero (u : ℤ_[p]ˣ) :
    (u : ℚ_[p]).valuation = 0 := by
  have hnorm : ‖(u : ℚ_[p])‖ = 1 := by
    simpa using (PadicInt.norm_units u)
  have hne : (u : ℚ_[p]) ≠ 0 := by
    intro h
    have hZ : (u : ℤ_[p]) = 0 := Subtype.ext (by simpa using h)
    exact u.ne_zero hZ
  have hval := Padic.norm_eq_zpow_neg_valuation (x := (u : ℚ_[p])) hne
  rw [hnorm] at hval
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp1
  have hz : (p : ℝ) ^ (-(u : ℚ_[p]).valuation) = 1 := hval.symm
  have hz0 : (p : ℝ) ^ (-(u : ℚ_[p]).valuation) = (p : ℝ) ^ (0 : ℤ) := by
    simpa using hz
  have hzero := (zpow_right_inj₀ hp0 hp1.ne').mp hz0
  linarith
#check zpUnit_valuation_eq_zero
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitValuationActual
end
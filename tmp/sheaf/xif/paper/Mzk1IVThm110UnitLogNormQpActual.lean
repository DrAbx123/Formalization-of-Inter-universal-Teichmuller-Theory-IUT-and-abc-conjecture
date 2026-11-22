import tmp.sheaf.xif.paper.Mzk1IVThm110UnitLogNormBoundActual
import Mathlib.NumberTheory.Padics.PadicNumbers
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormQpActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormBoundActual
/-- Qp principal units are within p^{-1} of 1. -/
theorem principalUnit_norm_sub_one_le_inv_p_Qp
    {p : Nat} [Fact p.Prime] (x : (Integers ℚ_[p])ˣ)
    (hx : x ∈ principalUnits (K := ℚ_[p])) :
    ‖(((x.val : Integers ℚ_[p]) : ℚ_[p]) - 1)‖ ≤ (p : ℝ)⁻¹ := by
  have hlt : ‖(((x.val : Integers ℚ_[p]) : ℚ_[p]) - 1)‖ < 1 :=
    (mem_principalUnits_iff (K := ℚ_[p]) x).mp hx
  have h := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one (p := p)
    (((x.val : Integers ℚ_[p]) : ℚ_[p]) - 1) 0).mp (by simpa using hlt)
  simpa using h
/-- unitLog norm bound over Qp for p ≥ 3. -/
theorem unitLog_norm_le_one_Qp
    {p : Nat} [Fact p.Prime] (hp3 : 3 ≤ p)
    (hcop : Nat.Coprime p (integralUnitExponent (K := ℚ_[p])))
    (u : (Integers ℚ_[p])ˣ) :
    ‖unitLog (K := ℚ_[p]) u‖ ≤ 1 := by
  apply unitLog_norm_le_one_of_principal_bound (K := ℚ_[p]) p
  · intro x hx
    have hxle := principalUnit_norm_sub_one_le_inv_p_Qp x hx
    have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    calc
      ‖(((x.val : Integers ℚ_[p]) : ℚ_[p]) - 1)‖ ≤ (p : ℝ)⁻¹ := hxle
      _ ≤ 1 / 3 := by
        rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num]
        exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr hp3r
  · exact hcop
#check principalUnit_norm_sub_one_le_inv_p_Qp
#check unitLog_norm_le_one_Qp
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormQpActual
end
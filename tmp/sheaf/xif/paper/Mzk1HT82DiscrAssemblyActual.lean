/- H-T / IUT IV Prop 1.3 全局化: root discriminant 塔恒等（natAbs 路线）+ 常数 21 核验。

* log_rootDiscr_eq_add: log rootDiscr L = log rootDiscr K + log|N(diff K L)|/[L:Q]
  （RationalDifferent 的 rootDiscr 归一化 donor + NumberField.absNorm_differentIdeal
   + 塔公式 discriminant_tower_formula_ringOfIntegers; 避开 Real.abs 改写）;
* 常数 21 数值核验（paper L1415-1416, E6: log2<=1, log3,log5<=2, 11+6+4=21）。 -/
import Mathlib.Tactic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalDifferent
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationActual
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationCoreActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT82DiscrAssemblyActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual

universe u

/-- **root discriminant 塔恒等**: log rootDiscr L = log rootDiscr K + log|N(diff K L)|/[L:Q]。 -/
theorem log_rootDiscr_eq_add
    {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]
    [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)] :
    Real.log (NumberField.rootDiscr L) =
      Real.log (NumberField.rootDiscr K) +
        Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) /
          (Module.finrank ℚ L : ℝ) := by
  have hL := IUT.ABCBridge.Arithmetic.RationalDifferent.log_absNorm_differentIdeal_div_finrank_eq_log_rootDiscr L
  have hK := IUT.ABCBridge.Arithmetic.RationalDifferent.log_absNorm_differentIdeal_div_finrank_eq_log_rootDiscr K
  rw [← hL, ← hK]
  have hcastL : ((Ideal.absNorm (differentIdeal ℤ (𝓞 L)) : ℕ) : ℝ) =
      ((discr L).natAbs : ℝ) := by
    rw [NumberField.absNorm_differentIdeal L (𝓞 L)]
  have hcastK : ((Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℕ) : ℝ) =
      ((discr K).natAbs : ℝ) := by
    rw [NumberField.absNorm_differentIdeal K (𝓞 K)]
  have htower := discriminant_tower_formula_ringOfIntegers (K := K) (L := L)
  have hnKL : (0 : ℝ) < ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) := by
    apply Nat.cast_pos.mpr
    exact Nat.pos_of_ne_zero (fun h0 =>
      differentIdeal_ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have hnK : (0 : ℝ) < ((discr K).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  have hprod : ((discr L).natAbs : ℝ) =
      ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) *
        ((discr K).natAbs : ℝ) ^ Module.finrank K L := by
    rw [htower]
    push_cast
    ring
  have hfL : (Module.finrank ℚ L : ℝ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
    exact_mod_cast hpos.ne'
  have hfK : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast hpos.ne'
  have hfinN : Module.finrank K L * Module.finrank ℚ K = Module.finrank ℚ L := by
    simpa [mul_comm] using (Module.finrank_mul_finrank ℚ K L)
  have hfin : (Module.finrank K L : ℝ) * (Module.finrank ℚ K : ℝ) = (Module.finrank ℚ L : ℝ) := by
    rw [← Nat.cast_mul, hfinN]
  rw [hcastL, hcastK, hprod]
  rw [Real.log_mul (ne_of_gt hnKL) (ne_of_gt (pow_pos hnK _)), Real.log_pow]
  push_cast
  field_simp
  linear_combination (Real.log ((discr K).natAbs : ℝ)) * hfin

/-! ## 常数 21 的数值核验（paper E6: log2<=1, log3,log5<=2） -/

/-- log 2 <= 1。 -/
theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

/-- log 3 <= 2。 -/
theorem log_three_le_two : Real.log 3 ≤ 2 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
  linarith

/-- 5 <= exp 2（用 exp 1 > 2.71828）。 -/
theorem five_le_exp_two : (5:ℝ) ≤ Real.exp 2 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hmul : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hmul]
  nlinarith

/-- log 5 <= 2。 -/
theorem log_five_le_two : Real.log 5 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 5)]
  exact five_le_exp_two

/-- log(2^11 * 3^3 * 5^2) = 11 log 2 + 3 log 3 + 2 log 5。 -/
theorem log_235const_eq :
    Real.log ((2:ℝ) ^ 11 * 3 ^ 3 * 5 ^ 2) =
      11 * Real.log 2 + 3 * Real.log 3 + 2 * Real.log 5 := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- **常数 21**: log(2^11 * 3^3 * 5^2) <= 21（paper L1415-1416: 11*1+3*2+2*2）。 -/
theorem log_235const_le_21 : Real.log ((2:ℝ) ^ 11 * 3 ^ 3 * 5 ^ 2) ≤ 21 := by
  rw [log_235const_eq]
  nlinarith [log_two_le_one, log_three_le_two, log_five_le_two]

#print axioms log_rootDiscr_eq_add
#print axioms log_two_le_one
#print axioms log_three_le_two
#print axioms log_five_le_two
#print axioms log_235const_eq
#print axioms log_235const_le_21

end LeanFormal.IUT.XiFPaper.Mzk1HT82DiscrAssemblyActual
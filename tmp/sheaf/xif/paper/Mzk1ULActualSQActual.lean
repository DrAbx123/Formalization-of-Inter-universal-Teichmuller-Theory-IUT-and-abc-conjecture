/- U-C Step (vi): actual 小素数乘积 s^Q 的候选定义与真引理（用于 hsQ 形状报告/后续接线）。

candidate: actualSQ X := ∏ p ∈ urSmallPrimeSet X, (p : ℝ)（urSmallPrimeSet = [1,X] 中素数筛选）。
已证: 正性、log 恒等（log ∏ = Σ log p）、因子上界（p ≤ X ⇒ 乘积 ≤ X^card）、
urSQ 的对数上界（urSQ_le ⇒ log(urSQ X) ≤ log X）。
注: paper 的 s^Q 是各 v_Q 的 s^F_{vQ} 支撑对象之积, 本文件只是「小素数集合乘积」
候选; per-place Prop1.3 部分仍是显式缺口（见 B 报告）。 -/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import tmp.sheaf.xif.paper.Mzk1URSmallPrimeActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULActualSQActual

open LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual

/-- actual 小素数乘积 s^Q（候选）: ∏_{p ∈ urSmallPrimeSet X} p。 -/
noncomputable def actualSQ (X : ℕ) : ℝ :=
  ∏ p ∈ urSmallPrimeSet X, (p : ℝ)

/-- actualSQ 正（每因子为素数 > 0）。 -/
theorem actualSQ_pos (X : ℕ) : 0 < actualSQ X := by
  unfold actualSQ
  apply Finset.prod_pos
  intro p hp
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  exact_mod_cast hprime.pos

/-- actualSQ 非负。 -/
theorem actualSQ_nonneg (X : ℕ) : 0 ≤ actualSQ X :=
  le_of_lt (actualSQ_pos X)

/-- log(∏ p) = Σ log p。 -/
theorem log_actualSQ (X : ℕ) :
    Real.log (actualSQ X) = ∑ p ∈ urSmallPrimeSet X, Real.log (p : ℝ) := by
  unfold actualSQ
  rw [Real.log_prod]
  intro p hp
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  exact_mod_cast hprime.ne_zero

/-- 每个元素 ≤ X ⇒ actualSQ X ≤ X^{card}。 -/
theorem actualSQ_le_pow_card (X : ℕ) :
    actualSQ X ≤ (X : ℝ) ^ (urSmallPrimeSet X).card := by
  unfold actualSQ
  have hle : ∀ p ∈ urSmallPrimeSet X, (p : ℝ) ≤ (X : ℝ) := by
    intro p hp
    have h1 : p ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    exact_mod_cast h1
  calc ∏ p ∈ urSmallPrimeSet X, (p : ℝ)
      ≤ ∏ _p ∈ urSmallPrimeSet X, (X : ℝ) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact Nat.cast_nonneg p
        · intro p hp
          exact hle p hp
    _ = (X : ℝ) ^ (urSmallPrimeSet X).card := by
        rw [Finset.prod_const]

/-- urSQ 的对数上界: 1 ≤ X ⇒ log(urSQ X) ≤ log X。 -/
theorem log_urSQ_le_log {X : ℕ} (hX : 1 ≤ X) :
    Real.log (urSQ X : ℝ) ≤ Real.log (X : ℝ) := by
  have hpos : (0 : ℝ) < (urSQ X : ℝ) := by
    exact_mod_cast urSQ_pos X
  have hle : (urSQ X : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast urSQ_le hX
  exact Real.log_le_log hpos hle

#print axioms actualSQ_pos
#print axioms actualSQ_nonneg
#print axioms log_actualSQ
#print axioms actualSQ_le_pow_card
#print axioms log_urSQ_le_log

end LeanFormal.IUT.XiFPaper.Mzk1ULActualSQActual

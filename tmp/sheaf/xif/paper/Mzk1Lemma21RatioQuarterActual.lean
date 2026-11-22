import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import Mathlib.Tactic

/-! # Mzk1Lemma21RatioQuarterActual — [Mzk1] Lemma 2.1(d) remaining arithmetic input: 0 < f0 <= 1/4

STEP 0 prior-art: corpus Lemma 2.1 lines 87-96 (n odd: f0 = |f(r)| = (m/(m+n))^m (n/(m+n))^n
<= 1/4); Mzk1Lemma21RatioOddActual (f0 = -f(r) = |f(r)|, f0 > 0), Mzk1P1MorphismInterfaceActual
(interface context).  This is pure real arithmetic; Mathlib pow_le_one₀ reused.

PROOF STRATEGY (complete, no case analysis needed): x := m/(m+n), y := n/(m+n) satisfy
x + y = 1, 0 <= x,y <= 1.  For m,n >= 1, x^m <= x and y^n <= y (since powers of x,y are
<= 1), hence x^m y^n <= x y <= ((x+y)/2)^2 = 1/4.  This covers all m,n >= 1 including
the paper's three cases. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioQuarterActual

/-- Power bound: for 0 <= x <= 1 and m >= 1, x^m <= x. -/
theorem pow_le_self_of_unit {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    x ^ m ≤ x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [pow_succ]
  have hk : x ^ k ≤ 1 := pow_le_one₀ hx0 hx1
  have hk0 : 0 ≤ x ^ k := pow_nonneg hx0 k
  nlinarith

/-- The paper's bound f0 = (m/(m+n))^m (n/(m+n))^n <= 1/4 for all m,n >= 1. -/
theorem belyi22_f0_quarter (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ((m : ℝ) / ((m + n : ℕ) : ℝ)) ^ m * ((n : ℝ) / ((m + n : ℕ) : ℝ)) ^ n ≤ 1 / 4 := by
  have hNpos : (0 : ℝ) < ((m + n : ℕ) : ℝ) := by positivity
  have hx0 : 0 ≤ (m : ℝ) / ((m + n : ℕ) : ℝ) := by positivity
  have hy0 : 0 ≤ (n : ℝ) / ((m + n : ℕ) : ℝ) := by positivity
  have hx1 : (m : ℝ) / ((m + n : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast Nat.le_add_right m n
  have hy1 : (n : ℝ) / ((m + n : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast Nat.le_add_left n m
  have hsum : (m : ℝ) / ((m + n : ℕ) : ℝ) + (n : ℝ) / ((m + n : ℕ) : ℝ) = 1 := by
    field_simp
    push_cast
    ring
  have hxm : ((m : ℝ) / ((m + n : ℕ) : ℝ)) ^ m ≤ (m : ℝ) / ((m + n : ℕ) : ℝ) :=
    pow_le_self_of_unit hx0 hx1 hm
  have hyn : ((n : ℝ) / ((m + n : ℕ) : ℝ)) ^ n ≤ (n : ℝ) / ((m + n : ℕ) : ℝ) :=
    pow_le_self_of_unit hy0 hy1 hn
  have hxy : (m : ℝ) / ((m + n : ℕ) : ℝ) * ((n : ℝ) / ((m + n : ℕ) : ℝ)) ≤ 1 / 4 := by
    nlinarith [sq_nonneg ((m : ℝ) / ((m + n : ℕ) : ℝ) - (n : ℝ) / ((m + n : ℕ) : ℝ)), hsum]
  calc ((m : ℝ) / ((m + n : ℕ) : ℝ)) ^ m * ((n : ℝ) / ((m + n : ℕ) : ℝ)) ^ n
      ≤ (m : ℝ) / ((m + n : ℕ) : ℝ) * ((n : ℝ) / ((m + n : ℕ) : ℝ)) :=
        mul_le_mul hxm hyn (pow_nonneg hy0 n) hx0
    _ ≤ 1 / 4 := hxy

#check pow_le_self_of_unit
#check belyi22_f0_quarter

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioQuarterActual
end

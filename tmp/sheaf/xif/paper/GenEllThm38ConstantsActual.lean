import Mathlib.Tactic

/-! # GenEllThm38ConstantsActual — Thm 3.8 effective-constant arithmetic (complete proofs)

STEP 0 prior-art: GenEll corpus Thm 3.8 (1145-1166), proof 1169-1199 (d0 = (3^2-1)(3^2-3)
(5^2-1)(5^2-5) = 23040); GenEll06Section3StatementsActual rows; GenEllThm38Effective
BoundsActual (constants + shapes).  No Mathlib shortcut needed: pure Nat arithmetic.

PAPER constants formalized: d0 = 23040 = |GL2(F_3) x GL2(F_5)|; its factorization
8*6*24*20; 900 = 2*3*12 + 8*100 (paper's estimate 2*3*12 + 8*100 <= 900); and the
Cor 4.4/4.3 coefficient comparisons 23040*100 vs 23040*900.  Complete proofs only.

LABEL: class-A arithmetic (complete proof). -/

namespace LeanFormal.IUT.XiFPaper.GenEllThm38ConstantsActual

/-- The order of GL2(F_3) is 48. -/
theorem gl2_f3_order : (3 ^ 2 - 1) * (3 ^ 2 - 3) = 48 := by norm_num

/-- The order of GL2(F_5) is 480. -/
theorem gl2_f5_order : (5 ^ 2 - 1) * (5 ^ 2 - 5) = 480 := by norm_num

/-- d0 = |GL2(F_3) x GL2(F_5)| = 23040. -/
theorem d0_eq : 48 * 480 = 23040 := by norm_num

/-- d0 = 8 * 6 * 24 * 20. -/
theorem d0_factor : 8 * 6 * 24 * 20 = 23040 := by norm_num

/-- The paper's estimate 2*3*12 + 8*100 <= 900. -/
theorem cor43_coefficient_estimate : 2 * 3 * 12 + 8 * 100 ≤ 900 := by norm_num

/-- 900 = 9*100 (paper's 23040*900 = 23040*100*9). -/
theorem nine_hundred_eq : 900 = 9 * 100 := by norm_num

/-- The Cor 4.3/4.4 coefficient comparison: 23040*100*9 = 23040*900. -/
theorem cor43_coefficient_eq : 23040 * 100 * 9 = 23040 * 900 := by ring

/-- log-diff/log-cond coefficient 6d: 2*3 = 6 (paper's factor). -/
theorem cor43_logdiff_coefficient : 2 * 3 = (6 : ℕ) := by norm_num

#check d0_eq
#check d0_factor
#check cor43_coefficient_estimate
#check cor43_coefficient_eq

end LeanFormal.IUT.XiFPaper.GenEllThm38ConstantsActual
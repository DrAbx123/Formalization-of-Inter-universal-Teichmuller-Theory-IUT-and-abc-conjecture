/- B1 analytic h (kurt): concrete values of the M2 B(d0) bound. Default heartbeats. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiB3AlgPointActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyConcreteActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB3AlgPointActual

/-- B(0) = 1. -/
theorem psiB_zero : psiB 0 = 1 := by
  unfold psiB
  norm_num

/-- B(1) = 3. -/
theorem psiB_one : psiB 1 = 3 := by
  unfold psiB
  norm_num

/-- B(2) = 9. -/
theorem psiB_two : psiB 2 = 9 := by
  unfold psiB
  norm_num

/-- B(d) >= 2 for d >= 1. -/
theorem two_le_psiB {d : ℕ} (hd : 1 ≤ d) : 2 ≤ psiB d := by
  unfold psiB
  have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2 : (2 : ℝ) ≤ 2 ^ d := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (by positivity : (0:ℝ) ≤ 2 ^ d))]

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiCauchyConcreteActual
end
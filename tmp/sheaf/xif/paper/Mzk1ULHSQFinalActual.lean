/- hsQ 逐位接口（paper L1572 形状，不 fake 全局界）:
  s^Q 对象 sQOf 在 Mzk1ULTripodalConductorActual; 本文件给出:
  - log_sQOf_le_of_perPlace: 逐位和上界 ⇒ log s^Q 上界;
  - hsQ_paper_shape: 若逐位界给出 2d_mod·S_ar+5+log l，则 log s^Q 同界（paper L1572/L1573 形式）。
  per-place 假设来自 absolute LocalConductorDifferentData 的逐位不同/导子估计（下一批）。 -/
import tmp.sheaf.xif.paper.Mzk1ULTripodalConductorActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHSQFinalActual

open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual

/-- 逐位和上界 ⇒ log s^Q 上界。 -/
theorem log_sQOf_le_of_perPlace (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) (C : ℝ)
    (h : ∑ p ∈ S, Real.log (p : ℝ) ≤ C) :
    Real.log (sQOf S : ℝ) ≤ C := by
  rw [log_sQOf_eq S hS]
  exact h

/-- paper L1572/L1573 的形状: log s^Q ≤ 2 d_mod S_ar + 5 + log l（由逐位界提供）。 -/
theorem hsQ_paper_shape (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0)
    (dmod Sar : ℝ) (hl : ℝ)
    (h : ∑ p ∈ S, Real.log (p : ℝ) ≤ 2 * dmod * Sar + 5 + Real.log hl) :
    Real.log (sQOf S : ℝ) ≤ 2 * dmod * Sar + 5 + Real.log hl :=
  log_sQOf_le_of_perPlace S hS _ h

/-- s^Q 非零（供除法/正性）。 -/
theorem sQOf_ne_zero (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) : sQOf S ≠ 0 :=
  ne_of_gt (sQOf_pos S hS)

#print axioms log_sQOf_le_of_perPlace
#print axioms hsQ_paper_shape
#print axioms sQOf_ne_zero

end LeanFormal.IUT.XiFPaper.Mzk1ULHSQFinalActual

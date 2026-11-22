/- O6 / M2: branch data extracted from the Belyi degree-reduction adapter:
a polynomial of positive degree whose values on the branch set and whose critical
values are rational. REUSE: `Mzk1G1O6BelyiReductionAdapterActual`,
`Mzk1G1PsiM2AnalyticActual.M2AnalyticTarget`. DEDUP: no such extraction existed. -/
import tmp.sheaf.xif.paper.Mzk1G1O6BelyiReductionAdapterActual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2BranchDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6BelyiReductionAdapterActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual

/-- A polynomial with nonzero derivative over a field has positive degree. -/
theorem natDegree_pos_of_derivative_ne_zero {q : Polynomial ℚ} (hq : q.derivative ≠ 0) :
    0 < q.natDegree := by
  by_contra h
  have h0 : q.natDegree = 0 := Nat.eq_zero_of_not_pos h
  apply hq
  rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.derivative_C]

/-- **Branch data from the Belyi degree reduction**: for a finite set of algebraic complex
numbers there is a polynomial of positive degree whose values on the set and whose
critical values are all rational numbers. -/
theorem exists_branch_belyi_data (Branch : Finset ℂ)
    (hBranch : ∀ z ∈ Branch, IsIntegral ℚ z) :
    ∃ q : Polynomial ℚ, 0 < q.natDegree ∧ q.derivative ≠ 0 ∧
      (∀ z ∈ Branch, ∃ c : ℚ, Polynomial.aeval z q = algebraMap ℚ ℂ c) ∧
      (∀ z : ℂ, Polynomial.aeval z q.derivative = 0 →
        ∃ c : ℚ, Polynomial.aeval z q = algebraMap ℚ ℂ c) := by
  obtain ⟨q, hq, hSq, hcrit⟩ := exists_belyiReduction_mem_range Branch hBranch
  refine ⟨q, natDegree_pos_of_derivative_ne_zero hq, hq, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, hc⟩ := hSq z hz
    exact ⟨c, hc.symm⟩
  · intro z hz
    obtain ⟨c, hc⟩ := hcrit z hz
    exact ⟨c, hc.symm⟩

#print axioms natDegree_pos_of_derivative_ne_zero
#print axioms exists_branch_belyi_data
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2BranchDataActual

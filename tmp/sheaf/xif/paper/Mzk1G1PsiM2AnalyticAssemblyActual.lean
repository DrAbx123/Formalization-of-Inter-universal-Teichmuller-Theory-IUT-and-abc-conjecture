/- B1-B support: assembly interface for `M2AnalyticTarget` (used by kurt's M2 recursion)
and the finite branch-set/special-set bridges built earlier (`M2AnalyticActual`,
`PsiBranchSetActual`). -/
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticActual
import tmp.sheaf.xif.paper.Mzk1G1PsiBranchSetActual
import tmp.sheaf.xif.paper.Mzk1G1ProtectedToZeroMapActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiBranchSetActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual

/-- **Assembly (elimination) rule for `M2AnalyticTarget`**: a single polynomial together
with the four component proofs yields the target. This is the interface the M2 recursion
produces step by step (not an additional assumption: it eliminates the definition). -/
theorem m2AnalyticTarget_of_witness (Branch : Finset ℂ) (q : Polynomial ℚ)
    (hdeg : 0 < q.natDegree)
    (hbranch : ∀ z ∈ Branch, Polynomial.aeval z q ∈ ({0, 1} : Set ℂ))
    (hcrit : ∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
      Polynomial.aeval z q ∈ ({0, 1} : Set ℂ))
    (h0 : Polynomial.aeval (0 : ℂ) q ∉ ({0, 1} : Set ℂ)) :
    M2AnalyticTarget Branch :=
  ⟨q, hdeg, hbranch, hcrit, h0⟩

/-- The branch-set membership interface: for any branch point, some witness polynomial has",
"value in {0,1} (the target's second conjunct, unpacked). -/
theorem m2AnalyticTarget_branch_mem (Branch : Finset ℂ)
    (h : M2AnalyticTarget Branch) {z : ℂ} (hz : z ∈ Branch) :
    ∃ q : Polynomial ℚ, Polynomial.aeval z q ∈ ({0, 1} : Set ℂ) := by
  obtain ⟨q, -, hbranch, -, -⟩ := h
  exact ⟨q, hbranch z hz⟩

/-- A branch point is finite: the finite branch set of `psiFixed` is a `Finset ℂ`. -/
theorem branchFixedFinite_finite (T : Finset ℚ) : (↑(branchFixedFinite T) : Set ℂ).Finite :=
  (branchFixedFinite T).finite_toSet

/-- Membership in the finite branch set of `psiFixed = inv ∘ psi`. -/
theorem branchFixedFinite_mem_iff {T : Finset ℚ} {z : ℂ} (hT : 2 ≤ T.card) :
    z ∈ branchFixedFinite T ↔
      ∃ w ∈ criticalValuesOverC (protectedToZeroPolynomial T), w ≠ 0 ∧ z = w⁻¹ := by
  rw [branchFixedFinite]
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨w, ⟨hw, hw0⟩, rfl⟩
    refine ⟨w, ?_, hw0, rfl⟩
    rw [← coe_branchValuesFinite T hT]
    exact Finset.mem_coe.mpr hw
  · rintro ⟨w, hw, hw0, rfl⟩
    refine ⟨w, ⟨?_, hw0⟩, rfl⟩
    exact Finset.mem_coe.mp (by rw [coe_branchValuesFinite T hT]; exact hw)

#print axioms m2AnalyticTarget_of_witness
#print axioms m2AnalyticTarget_branch_mem
#print axioms branchFixedFinite_finite
#print axioms branchFixedFinite_mem_iff
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticAssemblyActual-- t
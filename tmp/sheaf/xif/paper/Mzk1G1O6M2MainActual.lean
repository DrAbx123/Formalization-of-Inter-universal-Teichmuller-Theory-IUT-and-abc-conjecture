/- O6 / M2 main: the branch-to-target assembly, with the remaining Belyi pinning step as
an explicit named obligation (`M2BranchPinObligation`). REUSE:
- `Mzk1G1O6BelyiReductionAdapterActual.exists_belyiReduction_mem_range` (h existence),
- `Mzk1G1O6M2BranchDataActual.exists_branch_belyi_data` (positive degree + rational values),
- `tmp.external.ported.tauceti_belyi_core...CriticalValues` (`Polynomial.criticalValues`,
  `mem_criticalValues`) — imported, not ported,
- `Mzk1G1PsiM2AnalyticAssemblyActual.m2AnalyticTarget_of_witness` (target assembly),
- `Mzk1G1PsiM2AnalyticActual.M2AnalyticTarget` (target shape).
DEDUP: no existing bridge from `criticalValues ⊆ {0,1}` to the M2 critical-value field. -/
import tmp.sheaf.xif.paper.Mzk1G1O6M2BranchDataActual
import tmp.sheaf.xif.paper.Mzk1G1PsiM2AnalyticAssemblyActual
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.CriticalValues
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2MainActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6BelyiReductionAdapterActual
open LeanFormal.IUT.XiFPaper.Mzk1G1O6M2BranchDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticAssemblyActual

/-- **Critical-value field bridge**: if all critical values of `q` lie in `{0,1}`, then the
value at every critical point lies in `{0,1}`. -/
theorem m2_critical_field_of_subset {q : Polynomial ℚ} (hq' : q.derivative ≠ 0)
    (h : (q.criticalValues ℂ) ⊆ ({0, 1} : Set ℂ)) :
    ∀ z : ℂ, Polynomial.aeval z q.derivative = 0 →
      Polynomial.aeval z q ∈ ({0, 1} : Set ℂ) := by
  intro z hz
  apply h
  rw [Polynomial.mem_criticalValues]
  exact ⟨z, (Polynomial.mem_rootSet_of_ne hq').mpr hz, rfl⟩

/-- Assembly of `M2AnalyticTarget` from the four fields (elimination of the definition). -/
theorem m2AnalyticTarget_of_fields (Branch : Finset ℂ) (q : Polynomial ℚ)
    (hdeg : 0 < q.natDegree)
    (hbranch : ∀ z ∈ Branch, Polynomial.aeval z q ∈ ({0, 1} : Set ℂ))
    (hcrit : ∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative q) = 0 →
      Polynomial.aeval z q ∈ ({0, 1} : Set ℂ))
    (h0 : Polynomial.aeval (0 : ℂ) q ∉ ({0, 1} : Set ℂ)) :
    M2AnalyticTarget Branch :=
  m2AnalyticTarget_of_witness Branch q hdeg hbranch hcrit h0

/-- **The Belyi pinning obligation** (route §4.3, remaining gap): find a polynomial of
positive degree whose values on the branch set and critical values lie in `{0,1}` and whose
value at `0` avoids `{0,1}`. The degree reduction (`exists_branch_belyi_data`) provides the
rational-value input; the pinning itself is the named residual of the old Lemma 2.4 corpus
(`GChoiceCriticalInTarget` / `AvoidsPoint beta` / `UnramifiedOver` wiring). -/
def M2BranchPinObligation (Branch : Finset ℂ) : Prop :=
  ∃ q : Polynomial ℚ, 0 < q.natDegree ∧ q.derivative ≠ 0 ∧
    (∀ z ∈ Branch, Polynomial.aeval z q ∈ ({0, 1} : Set ℂ)) ∧
    (q.criticalValues ℂ) ⊆ ({0, 1} : Set ℂ) ∧
    Polynomial.aeval (0 : ℂ) q ∉ ({0, 1} : Set ℂ)

/-- **Main reduction**: the named pinning obligation yields `M2AnalyticTarget`. -/
theorem m2AnalyticTarget_of_pin (Branch : Finset ℂ) (h : M2BranchPinObligation Branch) :
    M2AnalyticTarget Branch := by
  obtain ⟨q, hdeg, hq', hbranch, hcrit, h0⟩ := h
  exact m2AnalyticTarget_of_fields Branch q hdeg hbranch
    (m2_critical_field_of_subset hq' hcrit) h0

#print axioms m2_critical_field_of_subset
#print axioms m2AnalyticTarget_of_fields
#print axioms m2AnalyticTarget_of_pin
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2MainActual

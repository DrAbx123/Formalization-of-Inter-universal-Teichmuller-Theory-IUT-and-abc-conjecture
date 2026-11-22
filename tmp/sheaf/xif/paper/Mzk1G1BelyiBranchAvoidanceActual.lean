import tmp.sheaf.xif.paper.GenEll16BelyiExistenceActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1BelyiBranchAvoidanceActual
open Polynomial

universe u
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Actual Belyi branch avoidance: every critical value lies in `{0,1}`. -/
theorem belyi_criticalValues_avoid {S : Finset K}
    (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L],
        ∀ x ∈ q.criticalValues L, x = 0 ∨ x = 1 := by
  obtain ⟨q, hdeg, hSq, hcrit⟩ :=
    LeanFormal.IUT.XiFPaper.GenEll16BelyiExistenceActual.genEll16_belyi_poly_aeval (K := K) hS
  refine ⟨q, hdeg, hSq, ?_⟩
  intro L _ _ x hx
  have hx01 := hcrit L hx
  simpa using hx01

#print axioms belyi_criticalValues_avoid
end LeanFormal.IUT.XiFPaper.Mzk1G1BelyiBranchAvoidanceActual
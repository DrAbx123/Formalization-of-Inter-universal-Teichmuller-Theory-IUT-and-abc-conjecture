import tmp.sheaf.xif.paper.GenEll16BelyiExistenceActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalMapActual

universe u
open Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Actual noncritical Belyi map existence: for a finite branch/protected set
of algebraic numbers there is a nonconstant polynomial map whose critical
values avoid everything outside `{0,1}`. -/
theorem noncriticalMap_exists {S : Finset K} (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
      ∀ (L : Type*) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ ({0, 1} : Set L) := by
  obtain ⟨q, hdeg, hSq, hcrit⟩ :=
    LeanFormal.IUT.XiFPaper.GenEll16BelyiExistenceActual.genEll16_belyi_poly_aeval (K := K) hS
  refine ⟨q, hdeg, hSq, ?_⟩
  intro L _ _ x hx
  exact hcrit L hx

#print axioms noncriticalMap_exists
end LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalMapActual
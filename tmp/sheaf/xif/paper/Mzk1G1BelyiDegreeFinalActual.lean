import tmp.sheaf.xif.paper.Mzk1G1NoncriticalMapActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1BelyiDegreeFinalActual
open Polynomial

universe u
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Final consumer: actual Belyi polynomial of positive degree. -/
theorem p7_belyiDegree_final {S : Finset K} (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree :=
  obtain ⟨q, hdeg, _, _⟩ :=
    LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalMapActual.noncriticalMap_exists (K := K) hS
  exact ⟨q, hdeg⟩

#print axioms p7_belyiDegree_final
end LeanFormal.IUT.XiFPaper.Mzk1G1BelyiDegreeFinalActual
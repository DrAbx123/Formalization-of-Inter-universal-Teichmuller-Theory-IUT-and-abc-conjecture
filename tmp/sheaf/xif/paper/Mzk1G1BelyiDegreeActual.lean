import tmp.sheaf.xif.paper.Mzk1G1NoncriticalMapActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1BelyiDegreeActual
open Polynomial

universe u
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Consumer: the actual Belyi polynomial has positive degree. -/
theorem belyiDegree_pos {S : Finset K} (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree := by
  obtain ⟨q, hdeg, _, _⟩ :=
    LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalMapActual.noncriticalMap_exists (K := K) hS
  exact ⟨q, hdeg⟩

#print axioms belyiDegree_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1BelyiDegreeActual
import tmp.sheaf.xif.paper.Mzk1G1BelyiProtectedActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalLimitActual

/-- Actual noncritical limit parameter: a point outside both the finite branch
set and the finite protected set. -/
theorem noncriticalLimit_exists {K : Type*} [Field K] [Infinite K]
    (branch protectedSet : Finset K) :
    ∃ t : K, t ∉ branch ∧ t ∉ protectedSet := by
  obtain ⟨t, ht⟩ := exists_notMem_finset (branch ∪ protectedSet)
  exact ⟨t, fun h => ht (Finset.mem_union_left _ h),
    fun h => ht (Finset.mem_union_right _ h)⟩

#print axioms noncriticalLimit_exists
end LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalLimitActual
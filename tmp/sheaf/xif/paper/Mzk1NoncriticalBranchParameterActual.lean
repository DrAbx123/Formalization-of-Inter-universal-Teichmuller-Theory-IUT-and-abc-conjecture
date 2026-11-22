import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1NoncriticalBranchParameterActual

/-- Actual noncritical parameter outside two finite sets (branch and protected). -/
theorem noncriticalBranchParameter_exists {K : Type*} [Field K] [Infinite K]
    (branch protectedSet : Finset K) :
    ∃ t : K, t ∉ branch ∧ t ∉ protectedSet := by
  classical
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (branch ∪ protectedSet)
  exact ⟨t, fun h => ht (Finset.mem_union_left _ h),
    fun h => ht (Finset.mem_union_right _ h)⟩

#print axioms noncriticalBranchParameter_exists
end LeanFormal.IUT.XiFPaper.Mzk1NoncriticalBranchParameterActual
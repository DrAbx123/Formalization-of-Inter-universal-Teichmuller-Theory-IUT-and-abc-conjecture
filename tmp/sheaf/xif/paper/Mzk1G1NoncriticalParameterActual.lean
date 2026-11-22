import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalParameterActual

/-- Actual noncritical parameter selection outside a finite protected set. -/
theorem noncriticalParameter_exists {K : Type*} [Field K] [Infinite K]
    (protectedSet : Finset K) :
    ∃ t : K, t ∉ protectedSet :=
  Infinite.exists_notMem_finset protectedSet

#print axioms noncriticalParameter_exists
end LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalParameterActual
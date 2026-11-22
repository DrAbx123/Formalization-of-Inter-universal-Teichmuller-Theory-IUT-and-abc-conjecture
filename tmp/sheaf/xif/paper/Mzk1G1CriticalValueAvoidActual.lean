import tmp.sheaf.xif.paper.GenEll16BelyiExistenceActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1CriticalValueAvoidActual
open Polynomial

universe u
variable {K : Type*} [Field K] [Algebra ℚ K]

/-- Actual critical-value avoidance for the Belyi polynomial: critical values
lie in `{0,1}`. -/
theorem criticalValueAvoid_exists {S : Finset K}
    (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ ({0, 1} : Set L) :=
  LeanFormal.IUT.XiFPaper.GenEll16BelyiExistenceActual.genEll16_belyi_poly_aeval hS

#print axioms criticalValueAvoid_exists
end LeanFormal.IUT.XiFPaper.Mzk1G1CriticalValueAvoidActual
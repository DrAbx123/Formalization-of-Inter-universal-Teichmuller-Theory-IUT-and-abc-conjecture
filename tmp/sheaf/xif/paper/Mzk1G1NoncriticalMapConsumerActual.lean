import tmp.sheaf.xif.paper.Mzk1G1NoncriticalMapActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalMapConsumerActual
open Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K] {S : Finset K}

/-- Consumer: actual noncritical Belyi data used through its critical-value
avoidance property. -/
theorem noncriticalMapConsumer (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
      ∀ (L : Type*) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ ({0, 1} : Set L) :=
  LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalMapActual.noncriticalMap_exists hS

#print axioms noncriticalMapConsumer
end LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalMapConsumerActual
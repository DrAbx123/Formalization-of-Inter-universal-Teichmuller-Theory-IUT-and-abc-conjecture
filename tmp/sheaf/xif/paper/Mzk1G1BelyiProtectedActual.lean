import tmp.sheaf.xif.paper.GenEll16BelyiExistenceActual
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1BelyiProtectedActual

universe u
universe u
open Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- A Belyi polynomial certificate for a finite protected set of algebraic
numbers: nonconstant, maps the set into `{0,1}`, critical values in `{0,1}`. -/
theorem belyi_protected_certificate {S : Finset K}
    (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ ({0, 1} : Set L) := by
  obtain ⟨q, hdeg, hSq, hcrit⟩ :=
    LeanFormal.IUT.XiFPaper.GenEll16BelyiExistenceActual.genEll16_belyi_poly_aeval (K := K) hS
  refine ⟨q, hdeg, hSq, ?_⟩
  intro L _ _ x hx
  exact hcrit L hx

/-- Actual protected-parameter avoidance: in an infinite field a finite union
of protected values is not all of the field. -/
theorem exists_parameter_avoiding_finset {K : Type*} [Field K] [Infinite K]
    (protectedSet : Finset K) :
    ∃ t : K, t ∉ protectedSet :=
  Infinite.exists_notMem_finset protectedSet

#print axioms belyi_protected_certificate
#print axioms exists_parameter_avoiding_finset
end LeanFormal.IUT.XiFPaper.Mzk1G1BelyiProtectedActual
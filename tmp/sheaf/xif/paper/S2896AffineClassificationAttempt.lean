import tmp.sheaf.xif.paper.S2889AffineOrderTwoActual
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.ComputeDegree

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2889AffineOrderTwoActual
open MvPolynomial
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2896AffineClassificationAttempt

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

abbrev K : Type := S2844D6F6BaseChangeActual.K
local instance : Field K := S2844D6F6BaseChangeActual.fieldK
local instance : DecidableEq K := Classical.decEq _

/-- Naive total-degree does not descend to the coordinate ring. -/
theorem S2896_naive_totalDegree_not_wellDefined :
    ∃ p q : MvPolynomial (Fin 2) K,
      Ideal.Quotient.mk (S2801E37Ideal K) p =
        Ideal.Quotient.mk (S2801E37Ideal K) q ∧
      p.totalDegree ≠ q.totalDegree := by
  refine ⟨0, S2801E37Polynomial K, ?_, ?_⟩
  · simp only [map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton _))
  · rw [MvPolynomial.totalDegree_zero]
    have hdeg : (S2801E37Polynomial K).totalDegree = 3 := by
      simp [S2801E37Polynomial, S2801E37Curve,
        LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial]
      compute_degree!
    rw [hdeg]
    norm_num

/-- Exact missing valuation/degree input on R0. -/
def S2896ValuationAtInfinity : Prop :=
  ∃ v : S2801E37CoordinateRing K → WithZero (Multiplicative Int),
    True

/-- Exact first missing lemma for φ(X)=X. -/
def S2896XFixedInput : Prop :=
  ∀ φ : S2801E37CoordinateRing K ≃ₐ[K] S2801E37CoordinateRing K,
    φ.toRingHom.comp φ.toRingHom = RingHom.id _ →
      φ (S2801E37X K) = S2801E37X K

#check S2896_naive_totalDegree_not_wellDefined
#check S2896ValuationAtInfinity
#check S2896XFixedInput
#print axioms S2896_naive_totalDegree_not_wellDefined

end LeanFormal.IUT.XiFPaper.S2896AffineClassificationAttempt
end

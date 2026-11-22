import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData

noncomputable section
set_option maxHeartbeats 4000000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2480QiActual

abbrev F : Type := AdjoinRoot (X ^ 2 + 1 : ℚ[X])

theorem S2480_irreducible : Irreducible (X ^ 2 + 1 : ℚ[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by
      rw [show (1 : ℚ[X]) = C 1 by simp]
      exact Polynomial.natDegree_X_pow_add_C
    simp [hdeg]
  · intro x hx
    rw [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at hx
    nlinarith [sq_nonneg x]

instance : Fact (Irreducible (X ^ 2 + 1 : ℚ[X])) := ⟨S2480_irreducible⟩

example : Field F := inferInstance
example : Algebra ℚ F := inferInstance

example : FiniteDimensional ℚ F := inferInstance
example : NumberField F := inferInstance


theorem S2480_hasSqrtNegOne : LeanFormal.IUT.HasSqrtNegOne F := by
  refine ⟨AdjoinRoot.root (X ^ 2 + 1 : ℚ[X]), ?_⟩
  have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : ℚ[X])
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one] at h
  linear_combination h

#print axioms S2480_hasSqrtNegOne

end LeanFormal.IUT.XiFPaper.S2480QiActual
end
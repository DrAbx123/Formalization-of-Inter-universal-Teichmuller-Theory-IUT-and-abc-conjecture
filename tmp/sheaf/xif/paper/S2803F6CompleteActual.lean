import tmp.sheaf.xif.paper.S2790F6Actual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2790F6Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2803F6CompleteActual

local instance s2803GaussianFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Conditional finite-dimensionality: if the E[6] coordinate set is finite,
then F6 = adjoin of those coordinates is finite-dimensional over Q(i). -/
theorem S2803_finiteDimensional_of_coords_finite
    (h : S2790CoordSet.Finite) :
    FiniteDimensional GaussianField S2790F6 := by
  letI : Finite S2790CoordSet := h.to_subtype
  exact IntermediateField.finiteDimensional_adjoin
    (K := GaussianField) (L := S2790L) (S := S2790CoordSet) (by
      intro x _
      exact (Algebra.IsAlgebraic.isAlgebraic (R := GaussianField) (A := S2790L) x).isIntegral)

#check S2803_finiteDimensional_of_coords_finite

end LeanFormal.IUT.XiFPaper.S2803F6CompleteActual
end
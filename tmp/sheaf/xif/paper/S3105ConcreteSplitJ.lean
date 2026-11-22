import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitMultiplicativeCurve
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample

noncomputable section
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3105ConcreteSplitJ

local instance : Fact (Irreducible
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The concrete split multiplicative curve has j = -1/10805. -/
theorem concreteSplitCurve_j :
    concreteSplitCurve.j = (-1 / 10805 : ℚ) := by
  rw [WeierstrassCurve.j, concreteSplitCurve_c₄]
  have hΔ : (concreteSplitCurve.Δ' : ℚ) = -10805 := by
    rw [WeierstrassCurve.coe_Δ', concreteSplitCurve_delta]
  have hinv : (↑concreteSplitCurve.Δ'⁻¹ : ℚ) = ((concreteSplitCurve.Δ' : ℚ))⁻¹ := by
    simp
  rw [hinv, hΔ]
  norm_num

/-- Base change to the Gaussian field preserves the j-invariant. -/
theorem S3105ConcreteSplitJ :
    (concreteSplitPuncturedCurve.baseChange GaussianField).jInvariant =
      algebraMap ℚ GaussianField (-1 / 10805) := by
  change (concreteSplitCurve.map (algebraMap ℚ GaussianField)).j =
    algebraMap ℚ GaussianField (-1 / 10805)
  rw [WeierstrassCurve.map_j, concreteSplitCurve_j]

#check concreteSplitCurve_j
#check S3105ConcreteSplitJ
#print axioms concreteSplitCurve_j
#print axioms S3105ConcreteSplitJ

end LeanFormal.IUT.XiFPaper.S3105ConcreteSplitJ
end

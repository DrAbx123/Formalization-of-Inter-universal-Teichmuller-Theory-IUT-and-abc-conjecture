import Mathlib
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S3108PMapEqAttempt

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S3108PMapEqAttempt
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S3108IsSplittingField

/-- Conditional splitting-field statement with base `ℚ`: if `root : F` satisfies
`root^2 = -1` and the roots of `p = X^2 + 1` generate `F` over `ℚ`, then
`F` is a splitting field of `p` over `ℚ`. -/
theorem S3108_isSplittingField (root : F) (hroot : root ^ 2 = -1)
    (hadjoin : Algebra.adjoin ℚ (p.rootSet F) = ⊤) :
    Polynomial.IsSplittingField ℚ F p := by
  refine ⟨?_, ?_⟩
  · rw [S3108_p_map_eq root hroot]
    have h2 : Splits ((Polynomial.X + Polynomial.C root : Polynomial F)) := by
      simpa [map_neg] using (Splits.X_sub_C (-root))
    exact (Splits.X_sub_C root).mul h2
  · exact hadjoin

#check S3108_isSplittingField
#print axioms S3108_isSplittingField

end LeanFormal.IUT.XiFPaper.S3108IsSplittingField
end

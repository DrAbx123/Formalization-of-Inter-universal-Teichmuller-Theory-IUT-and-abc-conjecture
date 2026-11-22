import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual
import LeanFormal.IUT.ABCBridge.Bridge.ThetaBoundToHeightWeight

/-! # S3131 prior-art reuse: ThetaBoundToHeightWeight vs our V2 comparison data -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual

namespace LeanFormal.IUT.XiFPaper.S3131ThetaBoundToHeightWeightReuseActual

universe u

/-- **PRIOR-ART MAPPING (proved):** our V2 epsilon-comparison data supplies exactly
the two hypothesis families of `heightWeightBound_of_normalizedVolumeComparison`
(the prior-art bridge that derives the ABC height-weight bound). This is the reuse
point: no new bridge proof is needed. -/
theorem v2Data_gives_normalizedVolumeComparison {X : Type u}
    {W : IQHullLogVolumeInterface X} {epsilon : Real} (heps : 0 < epsilon)
    (D : Cor312EpsilonArithmeticComparisonV2 W epsilon) :
    (∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * (W.logVolume (D.comparisonRegion a b c)).toReal) ∧
    (∃ D0 : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (D.comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D0) :=
  ⟨D.height_le_comparisonRegionVolume, D.regionVolume_le_normalizedWeight⟩

#check heightWeightBound_of_normalizedVolumeComparison
#check exists_oneAdd_sq_le_oneAdd
#check v2Data_gives_normalizedVolumeComparison

end LeanFormal.IUT.XiFPaper.S3131ThetaBoundToHeightWeightReuseActual
end
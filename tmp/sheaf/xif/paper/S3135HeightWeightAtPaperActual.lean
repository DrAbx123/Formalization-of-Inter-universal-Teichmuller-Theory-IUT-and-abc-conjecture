import LeanFormal.IUT.ABCBridge.Bridge.ThetaBoundToHeightWeight
import tmp.sheaf.xif.paper.S3135RegionRelativeObligationActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135HeightWeightAtPaperActual

/-- **Uniform height-vs-volume comparison at the PAPER height/weight functions**:
specialization of the production bridge `heightWeightBound_of_normalizedVolumeComparison`
(prior art: ThetaBoundToHeightWeight.lean:67; height/weight function layer:
ArithmeticDivisorDegree.lean:1214/1221/1225/1310/1613 heightWeight/hTerm/toricHeightWeight;
mainline already reuses this bridge in Cor312ToABCBridge).  Given the (b) shape
hypotheses on the actual paper height `Height.logHeight₁ (abcRationalPoint a c)` and
actual arithmetic weight `arithmeticWeight (abcRationalPoint a c)`, obtain the
version-2 additive bound.  This file only NAMES the specialization; no discharge claim. -/
theorem s3135_heightWeightBound_atPaperFunctions
    (volume : (delta : ℝ) → 0 < delta → ℕ → ℕ → ℕ → ℝ) (thetaBound : ℝ)
    (hweight_nonneg : ∀ (a b c : ℕ), IsABCTriple a b c →
      0 ≤ arithmeticWeight (abcRationalPoint a c))
    (hcomparison :
      ∀ (delta : ℝ) (hdelta : 0 < delta),
        (∀ (a b c : ℕ), IsABCTriple a b c →
          Height.logHeight₁ (abcRationalPoint a c) ≤
            (1 + delta) * volume delta hdelta a b c) ∧
          ∃ D, ∀ (a b c : ℕ), IsABCTriple a b c →
            volume delta hdelta a b c ≤
              (1 + delta) * arithmeticWeight (abcRationalPoint a c) + thetaBound + D)
    (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ A, ∀ (a b c : ℕ), IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  heightWeightBound_of_normalizedVolumeComparison
    (fun a b c => Height.logHeight₁ (abcRationalPoint a c))
    (fun a b c => arithmeticWeight (abcRationalPoint a c))
    volume thetaBound hweight_nonneg hcomparison epsilon heps

#check s3135_heightWeightBound_atPaperFunctions
end LeanFormal.IUT.XiFPaper.S3135HeightWeightAtPaperActual
end

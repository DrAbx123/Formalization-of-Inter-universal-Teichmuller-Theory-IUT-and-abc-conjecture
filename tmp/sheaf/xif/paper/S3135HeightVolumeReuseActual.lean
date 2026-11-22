import LeanFormal.IUT.ABCBridge.Bridge.ThetaBoundToHeightWeight

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135HeightVolumeReuseActual

/-- **Uniform height-vs-volume comparison, reused from the tree** (prior art
`ThetaBoundToHeightWeight.heightWeightBound_of_normalizedVolumeComparison`,
already used by mainline's Cor312ToABCBridge): the (b) shape hypotheses (height <=
(1+delta)*volume and volume <= (1+delta)*weight + theta + D uniformly) yield the
version-2 additive height/weight bound.  This file only names/reuses the production
bridge for the paper route; it does not reprove it. -/
theorem s3135_heightWeightBound_of_normalizedVolumeComparison
    {P : ℕ → ℕ → ℕ → Prop} (height weight : ℕ → ℕ → ℕ → ℝ)
    (volume : (delta : ℝ) → 0 < delta → ℕ → ℕ → ℕ → ℝ) (thetaBound : ℝ)
    (hweight_nonneg : ∀ (a b c : ℕ), P a b c → 0 ≤ weight a b c)
    (hcomparison :
      ∀ (delta : ℝ) (hdelta : 0 < delta),
        (∀ (a b c : ℕ), P a b c → height a b c ≤ (1 + delta) * volume delta hdelta a b c) ∧
          ∃ D, ∀ (a b c : ℕ), P a b c → volume delta hdelta a b c ≤ (1 + delta) * weight a b c + thetaBound + D)
    (epsilon : ℝ) (heps : 0 < epsilon) :
    ∃ A, ∀ (a b c : ℕ), P a b c → height a b c ≤ (1 + epsilon) * weight a b c + A :=
  LeanFormal.IUT.heightWeightBound_of_normalizedVolumeComparison
    height weight volume thetaBound hweight_nonneg hcomparison epsilon heps

#check s3135_heightWeightBound_of_normalizedVolumeComparison

end LeanFormal.IUT.XiFPaper.S3135HeightVolumeReuseActual
end

import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
/-! P3: exact product Haar decomposition for root extension product carrier. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3ProductHaarPiActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Product Haar of a product set is the product of the local Haar masses. -/
theorem productHaar_pi
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    rootExtensionProductHaar T (Set.pi Set.univ S) =
      ∏ b : Bad (nativePlaceSelection T), rootExtensionHaar T b (S b) := by
  unfold rootExtensionProductHaar
  rw [Measure.pi_pi]
/-- Normalized product log of a product set splits as the sum of local
normalized logs. -/
theorem productNormalizedLog_pi
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b))
    (hS : ∀ b, rootExtensionHaar T b (S b) ≠ 0)
    (hSfin : ∀ b, rootExtensionHaar T b (S b) ≠ ⊤)
    (hU : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hUfin : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    rootExtensionProductNormalizedLog T (Set.pi Set.univ S) =
      ∑ b : Bad (nativePlaceSelection T),
        (Real.log (rootExtensionHaar T b (S b)).toReal -
          Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) := by
  unfold rootExtensionProductNormalizedLog
  rw [productHaar_pi T S, rootExtensionProductHaar_unitBall T]
  rw [ENNReal.toReal_prod, ENNReal.toReal_prod]
  rw [Real.log_prod, Real.log_prod]
  · rw [Finset.sum_sub_distrib]
  · intro b _
    exact (ENNReal.toReal_pos (hU b) (hUfin b)).ne'
  · intro b _
    exact (ENNReal.toReal_pos (hS b) (hSfin b)).ne'
end LeanFormal.IUT.XiFPaper.Mzk1P3ProductHaarPiActual
end
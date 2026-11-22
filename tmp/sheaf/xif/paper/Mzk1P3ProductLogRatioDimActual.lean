import tmp.sheaf.xif.paper.Mzk1P3ProductLogRatioActual
import tmp.sheaf.xif.paper.Mzk1P3DupuyHiladoLogActual
/-! P3 #1 support: dimension-weighted product log-ratio decomposition. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3ProductLogRatioDimActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ProductHaarPiActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ProductLogRatioActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem productNormalizedLog_sub_div
    (S Tset : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b))
    (hS : ∀ b, rootExtensionHaar T b (S b) ≠ 0)
    (hSfin : ∀ b, rootExtensionHaar T b (S b) ≠ ⊤)
    (hT : ∀ b, rootExtensionHaar T b (Tset b) ≠ 0)
    (hTfin : ∀ b, rootExtensionHaar T b (Tset b) ≠ ⊤)
    (hU : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hUfin : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤)
    (D : ℝ) (hD : D ≠ 0) :
    (rootExtensionProductNormalizedLog T (Set.pi Set.univ S) -
        rootExtensionProductNormalizedLog T (Set.pi Set.univ Tset)) / D =
      (∑ b : Bad (nativePlaceSelection T),
        (Real.log (rootExtensionHaar T b (S b)).toReal -
          Real.log (rootExtensionHaar T b (Tset b)).toReal)) / D := by
  exact congrArg (fun x : ℝ => x / D)
    (productNormalizedLog_sub T S Tset hS hSfin hT hTfin hU hUfin)
end LeanFormal.IUT.XiFPaper.Mzk1P3ProductLogRatioDimActual
end
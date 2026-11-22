import tmp.sheaf.xif.paper.Mzk1P3DupuyHiladoLogActual
/-! P3 #1 support: difference of normalized product logs is the sum of local
normalized-log differences. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3ProductLogRatioActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ProductHaarPiActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem productNormalizedLog_sub
    (S Tset : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b))
    (hS : ∀ b, rootExtensionHaar T b (S b) ≠ 0)
    (hSfin : ∀ b, rootExtensionHaar T b (S b) ≠ ⊤)
    (hT : ∀ b, rootExtensionHaar T b (Tset b) ≠ 0)
    (hTfin : ∀ b, rootExtensionHaar T b (Tset b) ≠ ⊤)
    (hU : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ 0)
    (hUfin : ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) ≠ ⊤) :
    rootExtensionProductNormalizedLog T (Set.pi Set.univ S) -
        rootExtensionProductNormalizedLog T (Set.pi Set.univ Tset) =
      ∑ b : Bad (nativePlaceSelection T),
        (Real.log (rootExtensionHaar T b (S b)).toReal -
          Real.log (rootExtensionHaar T b (Tset b)).toReal) := by
  rw [productNormalizedLog_pi T S hS hSfin hU hUfin,
    productNormalizedLog_pi T Tset hT hTfin hU hUfin,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring
end LeanFormal.IUT.XiFPaper.Mzk1P3ProductLogRatioActual
end
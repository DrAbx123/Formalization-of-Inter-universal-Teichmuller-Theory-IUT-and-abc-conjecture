import tmp.sheaf.xif.paper.Mzk1P3ProductHaarPiActual
/-! P3: explicit product unit-ball log mass (Dupuy-Hilado input). -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1P3ProductUnitBallLogActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ProductHaarPiActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Log of the product unit-ball mass is the sum of local unit-ball logs. -/
theorem productUnitBall_logMass :
    Real.log (rootExtensionProductHaar T (rootExtensionProductUnitBall T)).toReal =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal := by
  rw [rootExtensionProductHaar_unitBall, ENNReal.toReal_prod]
  apply Real.log_prod
  intro b _
  exact (ENNReal.toReal_pos
    (ne_of_gt (rootExtensionUnitBall_measure_pos T b))
    (ne_of_lt (rootExtensionUnitBall_measure_lt_top T b))).ne'
end LeanFormal.IUT.XiFPaper.Mzk1P3ProductUnitBallLogActual
end
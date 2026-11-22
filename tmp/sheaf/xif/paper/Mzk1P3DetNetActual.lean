import tmp.sheaf.xif.paper.Mzk1P3NetGainP2Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3DetNetActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainLogActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
/-- Net quantity with the weighted determinant log as correction. -/
def detNet (G h : ℝ) : ℝ := netQuantity G h (p2WeightedDetLog T)
theorem detNet_le (G h : ℝ) : detNet T G h ≤ G - Real.log h := by
  unfold detNet netQuantity
  have hdet : p2WeightedDetLog T ≤ 0 := p2WeightedDetLog_nonpos T
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1P3DetNetActual
end
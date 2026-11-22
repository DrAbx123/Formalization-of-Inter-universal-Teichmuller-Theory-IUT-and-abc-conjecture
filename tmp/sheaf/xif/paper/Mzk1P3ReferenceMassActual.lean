import tmp.sheaf.xif.paper.Mzk1P3NetGainP2Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3ReferenceMassActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1P3NetGainP2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
def referenceMassTerm : ℝ := p2R13Exact T
theorem referenceMassTerm_nonneg : 0 ≤ referenceMassTerm T :=
  p2R13Exact_nonneg T
end LeanFormal.IUT.XiFPaper.Mzk1P3ReferenceMassActual
end
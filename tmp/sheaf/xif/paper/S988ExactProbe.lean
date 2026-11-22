import tmp.sheaf.xif.paper.S965FinalLCarrierTopologyActual
import tmp.sheaf.xif.paper.S976FiniteLogShellHaarActual
noncomputable section
open scoped BigOperators TensorProduct
namespace Probe988
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual LeanFormal.IUT.XiFPaper.PaperFinalLValuedTensorCarrierActual LeanFormal.IUT.XiFPaper.S945CarrierTopologyActual LeanFormal.IUT.XiFPaper.S965FinalLCarrierTopologyActual LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual LeanFormal.IUT.XiFPaper.S976FiniteLogShellHaarActual
open MeasureTheory
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l) [Fintype (Bad (nativePlaceSelection T))] (b : Bad (nativePlaceSelection T))
structure Data where
  topology : TopologicalSpace (FinalLValuedCarrier T b)
  [isTopologicalAddGroup : @IsTopologicalAddGroup (FinalLValuedCarrier T b) _ topology]
  [locallyCompactSpace : @LocallyCompactSpace (FinalLValuedCarrier T b) topology]
  measurableSpace : MeasurableSpace (FinalLValuedCarrier T b)
  [borelSpace : @BorelSpace (FinalLValuedCarrier T b) topology measurableSpace]
  measure : Measure (FinalLValuedCarrier T b)
  [isAddHaar : @Measure.IsAddHaarMeasure (FinalLValuedCarrier T b) _ topology measurableSpace measure]
  unitRegion : Set (FinalLValuedCarrier T b)
  unit_pos : 0 < measure unitRegion
  unit_lt_top : measure unitRegion < ⊤
end Probe988
end

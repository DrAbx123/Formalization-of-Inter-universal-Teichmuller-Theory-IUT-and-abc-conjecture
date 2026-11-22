import tmp.sheaf.xif.paper.PaperFinalLValuedThetaIndHullActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction LeanFormal.IUT.N8Closure LeanFormal.IUT.XiFPaper.PaperFinalLValuedThetaIndHullActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
#synth TopologicalSpace (Carrier T b)
#synth TopologicalSpace (FinalLValuedCarrier T b)

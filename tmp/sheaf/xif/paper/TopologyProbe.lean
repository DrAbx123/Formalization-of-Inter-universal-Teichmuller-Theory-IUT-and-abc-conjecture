import tmp.sheaf.xif.paper.PaperLevelXiFTargetBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
#check (inferInstance : TopologicalSpace (qVFamTensorBlock T b))
#check borel (qVFamTensorBlock T b)

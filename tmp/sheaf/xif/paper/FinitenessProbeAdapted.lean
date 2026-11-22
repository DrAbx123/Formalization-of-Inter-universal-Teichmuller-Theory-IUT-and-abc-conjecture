import tmp.sheaf.xif.paper.PaperLevelXiFTargetBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
#check (inferInstance : Finite (NumberField.FinitePlace T.arithmetic.Fmod))
#check (inferInstance : Fintype (NumberField.FinitePlace T.arithmetic.Fmod))
#check (inferInstance : Finite (Bad (nativePlaceSelection T)))

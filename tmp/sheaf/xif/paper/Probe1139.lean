import tmp.sheaf.xif.paper.S1116ERootStackDVRInstanceActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldIntegralUnits
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
#synth IsFractionRing (Integers (rootStackExtension T b)) (rootStackExtension T b)
#check IsFractionRing.injective

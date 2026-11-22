
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2190RootSourceConditionsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

#check tateCurveComparison (T := T) (b := b)
#check tatePointComparison (T := T) (b := b)
#check pointEquiv (T := T) (b := b)
#check pointEquiv_mk (T := T) (b := b)
#check S2190QSquareSource (T := T) (b := b)
#check S2190QLthPowerSource (T := T) (b := b)

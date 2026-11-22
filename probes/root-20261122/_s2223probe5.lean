
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2190RootSourceConditionsActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual

namespace S2223Probe

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

example : Algebra.IsAlgebraic T.arithmetic.K (Kv T b) := by
  letI : Module.Finite T.arithmetic.K (Kv T b) :=
    moduleFinite_completionAlgebra (k := T.arithmetic.K) (sectionKPlace T b)
  infer_instance

end S2223Probe
end

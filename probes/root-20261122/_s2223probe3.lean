
import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S2190RootSourceConditionsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual

namespace S2223Probe

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

example (c : Fin 2 → ZMod l.value) :
    (Matrix.GeneralLinearGroup.toLin (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))).toLinearEquiv c = c := by
  simp [Matrix.GeneralLinearGroup.toLin]

end S2223Probe
end

import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2744PerPlaceRegionAllCoordsActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2753C3RegionAllClosedActual

open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

theorem C3PerPlaceUpdateRegionAll_isClosed :
    IsClosed (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :=
  isClosed_perPlaceUpdateRegionAll (p := C3.p) (ι := C3.tensorIndex)
    (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)
    (C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e)
    (C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e)

#check C3PerPlaceUpdateRegionAll_isClosed

end LeanFormal.IUT.XiFPaper.S2753C3RegionAllClosedActual
end

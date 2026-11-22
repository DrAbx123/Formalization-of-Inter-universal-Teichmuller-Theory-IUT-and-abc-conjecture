import tmp.sheaf.xif.paper.S2727V2RegionTarget
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S2727V2AssemblyActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726C3PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2727V2RegionTarget
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]
local instance s2727aMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2727aBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

noncomputable def S2727C3HullData :
    IQHullLogVolumeInterface (C3LogShellTensorBlock C3) :=
  Classical.choose
    (exists_arithmeticTupleIQHullLogVolumeInterface
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple)
      (actualC3LogShellTensorHaar C3))

#check S2727C3HullData
#check comparisonRegion
#check comparisonRegionVolume
#check hvolTarget
#check hheightTarget


theorem S2727C3HullData_logVolume :
    (S2727C3HullData C3).logVolume =
      haarLogVolume (actualC3LogShellTensorHaar C3) :=
  (Classical.choose_spec
    (exists_arithmeticTupleIQHullLogVolumeInterface
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple)
      (actualC3LogShellTensorHaar C3))).2.2

theorem S2727HvolActual : hvolTarget C3 T e := rfl

#check S2727C3HullData_logVolume
#check S2727HvolActual
#print axioms S2727HvolActual

end LeanFormal.IUT.XiFPaper.S2727V2AssemblyActual
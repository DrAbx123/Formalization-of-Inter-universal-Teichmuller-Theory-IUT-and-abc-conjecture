import tmp.sheaf.xif.paper.S2762C3ComparisonDataInterfaceActual
import tmp.sheaf.xif.paper.S2747C3NormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S2761C3NormalizedThetaPilotLogVolumeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2767C3ComparisonDataConsumerActual

open MeasureTheory
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2747C3NormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2761C3NormalizedThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2762C3ComparisonDataInterfaceActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measW : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelW : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem c3ComparisonRegionData_logVolume_eq_theta :
    (c3ComparisonRegionData (l := l) (V := V) (I := I) C3 T e).logVolume =
      c3NormalizedThetaPilotLogVolume (l := l) (V := V) (I := I) C3 T e := rfl

theorem c3ComparisonRegionData_logVolume_nonneg :
    0 ≤ (c3ComparisonRegionData (l := l) (V := V) (I := I) C3 T e).logVolume :=
  c3NormalizedThetaPilotLogVolume_nonneg (l := l) (V := V) (I := I) C3 T e

theorem c3ComparisonRegionData_region_eq :
    (c3ComparisonRegionData (l := l) (V := V) (I := I) C3 T e).region =
      C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e := rfl

#check c3ComparisonRegionData_logVolume_eq_theta
end LeanFormal.IUT.XiFPaper.S2767C3ComparisonDataConsumerActual
end

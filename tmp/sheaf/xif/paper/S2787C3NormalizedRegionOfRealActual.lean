import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2787C3NormalizedRegionOfRealActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measG : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelG : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance normFinite : IsFiniteMeasureOnCompacts
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
  c3NormalizedTensorHaar_isFiniteMeasureOnCompacts (l := l) (V := V) (I := I) C3

theorem c3NormalizedRegion_measure_eq_ofReal :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) =
      ENNReal.ofReal ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) :=
  (ENNReal.ofReal_toReal (ne_of_lt (c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e))).symm

theorem c3NormalizedRegion_toReal_eq :
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal =
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal := rfl

#check c3NormalizedRegion_measure_eq_ofReal
end LeanFormal.IUT.XiFPaper.S2787C3NormalizedRegionOfRealActual
end

import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.S2741ComparisonVolumeEqLogGenericActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2747C3NormalizedLogVolumeActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2741ComparisonVolumeEqLogGenericActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance s2747Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2747Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

noncomputable def c3NormalizedComparisonRegionLogVolume : ℝ :=
  (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal

theorem c3NormalizedRegionLogVolume_eq_log :
    c3NormalizedComparisonRegionLogVolume (l := l) (V := V) (I := I) C3 T e =
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) := by
  unfold c3NormalizedComparisonRegionLogVolume
  exact vol_eq_log_of_haarLogVolume_toReal
    (μ := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (vol := (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)
    (S := C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)
    rfl
    (ne_of_lt (c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e))
    (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)

#check c3NormalizedRegionLogVolume_eq_log
end LeanFormal.IUT.XiFPaper.S2747C3NormalizedLogVolumeActual
end

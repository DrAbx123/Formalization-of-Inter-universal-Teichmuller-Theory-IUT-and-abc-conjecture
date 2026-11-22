import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2910C3NormalizedHvolConsumerActual

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
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCE : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCE : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

noncomputable def c3NormalizedComparisonRegionVolume : ℝ :=
  (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal

def c3NormalizedHvolTarget : Prop :=
  c3NormalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
    (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal

theorem c3NormalizedHvolTarget_holds :
    c3NormalizedHvolTarget (l := l) (V := V) (I := I) C3 T e := rfl

theorem c3NormalizedComparisonRegionVolume_eq_log :
    c3NormalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) := by
  have hfin := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  have hge1 := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
  rw [c3NormalizedComparisonRegionVolume]
  rw [haarLogVolume_of_lt_top hfin]
  rw [ENNReal.toReal_ofReal (Real.log_nonneg hge1)]

#check c3NormalizedHvolTarget_holds
#check c3NormalizedComparisonRegionVolume_eq_log
end LeanFormal.IUT.XiFPaper.S2910C3NormalizedHvolConsumerActual
end

import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2784C3NormalizedRegionHaarLogZeroIffActual

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
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measD : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelD : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem c3NormalizedRegion_haarLog_eq_zero_iff :
    haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) = 0 ↔
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) = 1 := by
  have hfin := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  have hge1 := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
  have hpos : 0 < (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal :=
    lt_of_lt_of_le zero_lt_one hge1
  constructor
  · intro h
    rw [haarLogVolume_of_lt_top hfin] at h
    have hlog_nonneg : 0 ≤ Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) :=
      Real.log_nonneg hge1
    have hle : Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp h
    have hlog0 : Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) = 0 :=
      le_antisymm hle hlog_nonneg
    have hto : (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal = 1 := by
      rcases (Real.log_eq_zero.mp hlog0) with hzero | h1 | hneg
      · exfalso
        linarith [hpos, hzero]
      · exact h1
      · exfalso
        linarith [hpos, hneg]
    rw [← ENNReal.ofReal_toReal (ne_of_lt hfin), hto]
    simp
  · intro h
    rw [haarLogVolume_of_lt_top hfin, h]
    simp

#check c3NormalizedRegion_haarLog_eq_zero_iff
end LeanFormal.IUT.XiFPaper.S2784C3NormalizedRegionHaarLogZeroIffActual
end

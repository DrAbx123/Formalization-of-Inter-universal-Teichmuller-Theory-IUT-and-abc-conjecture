import tmp.sheaf.xif.paper.S2749C3NormalizedHaarScalingActual
import tmp.sheaf.xif.paper.S2747C3NormalizedLogVolumeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2750C3NormalizedRealLogScalingActual

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
open LeanFormal.IUT.XiFPaper.S2747C3NormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2749C3NormalizedHaarScalingActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance s2750Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2750Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance s2750SMul :
    SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

theorem c3NormalizedRegion_realLogVolume_smul
    (u : ℚ_[C3.p]ˣ) :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 => ((u : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) +
        Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ)) := by
  have hscale := c3NormalizedTensorHaar_scaling (l := l) (V := V) (I := I) C3 T e
    u (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)
  have hfinite := c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e
  have hge1 := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
  have hne_real : (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hge1)
  have hcharpos : 0 < (distribHaarChar (C3LogShellTensorBlock C3) u : ℝ≥0) :=
    distribHaarChar_pos (A := C3LogShellTensorBlock C3) (g := u)
  have hcharpos_real : (0 : ℝ) < (distribHaarChar (C3LogShellTensorBlock C3) u : ℝ) := by
    exact_mod_cast hcharpos
  rw [hscale, ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [mul_comm ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ))
    ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)]
  rw [Real.log_mul hne_real (ne_of_gt hcharpos_real)]

#check c3NormalizedRegion_realLogVolume_smul
end LeanFormal.IUT.XiFPaper.S2750C3NormalizedRealLogScalingActual
end

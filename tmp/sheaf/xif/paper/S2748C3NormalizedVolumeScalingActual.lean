import tmp.sheaf.xif.paper.S2747C3NormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S2742VolumeScalingGenericActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2748C3NormalizedVolumeScalingActual

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
open LeanFormal.IUT.XiFPaper.S2742VolumeScalingGenericActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance s2748Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2748Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance s2748SMul :
    SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

theorem c3NormalizedRegionLogVolume_nonneg :
    0 ≤ c3NormalizedComparisonRegionLogVolume (l := l) (V := V) (I := I) C3 T e := by
  rw [c3NormalizedRegionLogVolume_eq_log]
  exact Real.log_nonneg
    (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)

theorem c3NormalizedRegionLogVolume_smul
    (u : ℚ_[C3.p]ˣ) (c : ℝ≥0)
    (hscale : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (u • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) =
      (c : ENNReal) * c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e))
    (hcpos : 0 < c)
    (hfinite' : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (u • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ≠ ⊤)
    (hge1' : 1 ≤ (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (u • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) :
    (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
        (u • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal =
      c3NormalizedComparisonRegionLogVolume (l := l) (V := V) (I := I) C3 T e +
        Real.log (c : ℝ) := by
  exact vol_scaling_of_haarLogVolume
    (μ := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (vol := c3NormalizedComparisonRegionLogVolume (l := l) (V := V) (I := I) C3 T e)
    (vol' := (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (u • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)
    (S := C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)
    (S' := u • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)
    (c := c)
    (by unfold c3NormalizedComparisonRegionLogVolume; rfl) rfl
    (ne_of_lt (c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e))
    (c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e)
    hfinite' hge1' hscale hcpos

#check c3NormalizedRegionLogVolume_nonneg
#check c3NormalizedRegionLogVolume_smul
end LeanFormal.IUT.XiFPaper.S2748C3NormalizedVolumeScalingActual
end

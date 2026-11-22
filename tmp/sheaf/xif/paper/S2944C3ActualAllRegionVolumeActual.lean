import tmp.sheaf.xif.paper.S2756C3HaarNormalizationBridgeActual
import tmp.sheaf.xif.paper.S2754C3RegionAllHaarFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2944C3ActualAllRegionVolumeActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2754C3RegionAllHaarFiniteActual
open LeanFormal.IUT.XiFPaper.S2756C3HaarNormalizationBridgeActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measDG : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelDG : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

noncomputable def c3NormalizedToActualScalar : ℝ≥0 :=
  (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3).addHaarScalarFactor
    (actualC3LogShellTensorHaar C3)

theorem c3NormalizedToActualScalar_pos :
    0 < c3NormalizedToActualScalar (l := l) (V := V) (I := I) C3 :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (actualC3LogShellTensorHaar C3)

/-- actual-Haar real log-volume on the full-coordinate comparison region. -/
noncomputable def c3ActualComparisonRegionVolume : ℝ :=
  Real.log ((actualC3LogShellTensorHaar C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)

/-- Pure normalization shift between actual-Haar and normalized real log-volumes
on the same (all-coordinates) region. -/
noncomputable def c3NormalizationShift : ℝ :=
  c3ActualComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e -
    c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e

theorem c3NormalizationShift_eq_neg_log_scalar :
    c3NormalizationShift (l := l) (V := V) (I := I) C3 T e =
      - Real.log ((c3NormalizedToActualScalar (l := l) (V := V) (I := I) C3 : ℝ)) := by
  have hspos : (0 : ℝ) < (c3NormalizedToActualScalar (l := l) (V := V) (I := I) C3 : ℝ) := by
    exact_mod_cast c3NormalizedToActualScalar_pos (l := l) (V := V) (I := I) C3
  have hc : ((c3NormalizedToActualScalar (l := l) (V := V) (I := I) C3 : ℝ)) ≠ 0 := ne_of_gt hspos
  have h := c3NormalizedTensorHaar_apply_eq_smul_actual (l := l) (V := V) (I := I) C3
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)
  have hb : actualC3LogShellTensorHaar C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ≠ ⊤ :=
    ne_of_lt (C3PerPlaceUpdateRegionAll_haar_finite (l := l) (V := V) (I := I) C3 T e)
  have hsa : (c3NormalizedToActualScalar (l := l) (V := V) (I := I) C3 : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  have hto : (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal =
      (c3NormalizedToActualScalar (l := l) (V := V) (I := I) C3 : ℝ) *
        (actualC3LogShellTensorHaar C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal := by
    rw [h, ENNReal.toReal_mul, ENNReal.coe_toReal]
    simp only [c3NormalizedToActualScalar]
  have hne_n : (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal ≠ 0 := by
    have hge1 := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hge1)
  have ha : (actualC3LogShellTensorHaar C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal =
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal /
        (c3NormalizedToActualScalar (l := l) (V := V) (I := I) C3 : ℝ) := by
    rw [eq_div_iff hc]
    rw [mul_comm]
    exact hto.symm
  unfold c3NormalizationShift c3ActualComparisonRegionVolume
  rw [ha]
  rw [c3ComparisonRegionVolume_eq (l := l) (V := V) (I := I) C3 T e]
  rw [Real.log_div hne_n hc]
  ring

#check c3NormalizationShift_eq_neg_log_scalar
end LeanFormal.IUT.XiFPaper.S2944C3ActualAllRegionVolumeActual
end

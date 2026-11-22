import tmp.sheaf.xif.paper.S2942C3HheightShiftDataActual
import tmp.sheaf.xif.paper.S2727V2RegionTarget
import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2943C3NormalizationDeltaActual

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
open LeanFormal.IUT.XiFPaper.S2727V2RegionTarget
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2934C3NormalizedHheightInterfaceActual
open LeanFormal.IUT.XiFPaper.S2937C3HheightNormalizationBridgeConsumer
open LeanFormal.IUT.XiFPaper.S2939C3HheightDataInterfaceActual
open LeanFormal.IUT.XiFPaper.S2941C3HheightShiftBridgeActual
open LeanFormal.IUT.XiFPaper.S2942C3HheightShiftDataActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measDF : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelDF : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Total comparison-volume bridge constant between S2727V2's actual-Haar
support≤1 comparison volume and the normalized all-coordinates comparison
volume.  It absorbs BOTH the region change and the Haar normalization;
it is NOT pure -log scalar.  Pure normalization part: S2944 c3NormalizationShift;
region-change part: S2945 c3RegionChangeShift. -/
noncomputable def c3NormalizationDelta : ℝ :=
  comparisonRegionVolume (l := l) (V := V) (I := I) C3 T e -
    c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e

theorem c3ComparisonRegionVolume_eq_add_normalizationDelta :
    comparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
      c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e +
        c3NormalizationDelta (l := l) (V := V) (I := I) C3 T e := by
  unfold c3NormalizationDelta
  ring

theorem hheightTarget_of_normalizedBound
    {height eps C : ℝ}
    (h : height ≤ (1 + eps) * c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e + C) :
    hheightTarget (l := l) (V := V) (I := I) C3 T e
      height eps (C - (1 + eps) * c3NormalizationDelta (l := l) (V := V) (I := I) C3 T e) :=
  C3HheightShiftData.toHheightTarget (l := l) (V := V) (I := I) C3 T e
    ({ height := height, eps := eps, C := C,
       delta := c3NormalizationDelta (l := l) (V := V) (I := I) C3 T e,
       hvol := c3ComparisonRegionVolume_eq_add_normalizationDelta (l := l) (V := V) (I := I) C3 T e,
       bound := h } : C3HheightShiftData (l := l) (V := V) (I := I) C3 T e)

#check c3ComparisonRegionVolume_eq_add_normalizationDelta
#check hheightTarget_of_normalizedBound
end LeanFormal.IUT.XiFPaper.S2943C3NormalizationDeltaActual
end

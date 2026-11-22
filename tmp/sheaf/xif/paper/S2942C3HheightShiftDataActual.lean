import tmp.sheaf.xif.paper.S2941C3HheightShiftBridgeActual
import tmp.sheaf.xif.paper.S2939C3HheightDataInterfaceActual
import tmp.sheaf.xif.paper.S2934C3NormalizedHheightInterfaceActual
import tmp.sheaf.xif.paper.S2790C3ComparisonRegionVolumeInterfaceActual
import tmp.sheaf.xif.paper.S2727V2RegionTarget
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2942C3HheightShiftDataActual

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
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measDE : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelDE : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Height data in the normalized comparison volume scale, plus the additive
normalization shift `delta` between actual and normalized log-volumes. -/
structure C3HheightShiftData where
  height : ℝ
  eps : ℝ
  C : ℝ
  delta : ℝ
  hvol : comparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
    c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e + delta
  bound : height ≤ (1 + eps) * c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e + C

theorem C3HheightShiftData.toHheightTarget
    (D : C3HheightShiftData (l := l) (V := V) (I := I) C3 T e) :
    hheightTarget (l := l) (V := V) (I := I) C3 T e
      D.height D.eps (D.C - (1 + D.eps) * D.delta) :=
  hheightTarget_of_c3NormalizedHheightTarget_shift (l := l) (V := V) (I := I) C3 T e
    D.delta D.hvol (c3NormalizedHheightTarget_of_le (l := l) (V := V) (I := I) C3 T e D.bound)

/-- All-eps shifted data, matching S2721's shape. -/
def C3HheightAllEpsShiftData (height delta : ℝ) : Prop :=
  ∀ (eps : ℝ), 0 < eps → ∃ C : ℝ,
    height ≤ (1 + eps) * c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e + C

theorem C3HheightAllEpsShiftData.toHheightTarget
    {height delta : ℝ}
    (D : C3HheightAllEpsShiftData (l := l) (V := V) (I := I) C3 T e height delta)
    (hvol : comparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
      c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e + delta)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, hheightTarget (l := l) (V := V) (I := I) C3 T e
      height eps (C - (1 + eps) * delta) :=
  ⟨Classical.choose (D eps heps),
    hheightTarget_of_c3NormalizedHheightTarget_shift (l := l) (V := V) (I := I) C3 T e
      delta hvol
      (c3NormalizedHheightTarget_of_le (l := l) (V := V) (I := I) C3 T e
        (Classical.choose_spec (D eps heps)))⟩

#check C3HheightShiftData.toHheightTarget
#check C3HheightAllEpsShiftData.toHheightTarget
end LeanFormal.IUT.XiFPaper.S2942C3HheightShiftDataActual
end

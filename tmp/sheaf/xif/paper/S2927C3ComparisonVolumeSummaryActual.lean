import tmp.sheaf.xif.paper.S2749C3NormalizedHaarScalingActual
import tmp.sheaf.xif.paper.S2794C3NormalizedUnitLatticeInvarianceActual
import tmp.sheaf.xif.paper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
import tmp.sheaf.xif.paper.S2913C3ComparisonRegionVolumeHvolEqConsumer
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2927C3ComparisonVolumeSummaryActual

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
open LeanFormal.IUT.XiFPaper.S2749C3NormalizedHaarScalingActual
open LeanFormal.IUT.XiFPaper.S2774C3NormalizedThetaVolumeNonnegActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2794C3NormalizedUnitLatticeInvarianceActual
open LeanFormal.IUT.XiFPaper.S2910C3NormalizedHvolConsumerActual
open LeanFormal.IUT.XiFPaper.S2911C3NormalizedThetaVolumeConsumerActual
open LeanFormal.IUT.XiFPaper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
open LeanFormal.IUT.XiFPaper.S2913C3ComparisonRegionVolumeHvolEqConsumer
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCR : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCR : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3ComparisonVolume_scaling_summary
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    (u : ℚ_[C3.p]ˣ) (w : (PadicInt C3.p)ˣ) :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 => ((u : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) =
        (distribHaarChar (C3LogShellTensorBlock C3) u : ENNReal) *
          c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
            (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ∧
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 =>
          ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
          (tensorLattice (p := C3.p)
            (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) :
            Set (C3LogShellTensorBlock C3))) = 1 ∧
      c3NormalizedThetaVolume (l := l) (V := V) (I := I) C3 T e =
        c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e ∧
      c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
        c3NormalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e :=
  ⟨c3NormalizedTensorHaar_scaling (l := l) (V := V) (I := I) C3 T e u
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e),
    c3NormalizedTensorHaar_unit_smul_lattice (l := l) (V := V) (I := I) C3 T e w,
    C3NormalizedThetaVolume_eq_normalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e,
    C3ComparisonRegionVolume_eq_normalizedHvolVolume (l := l) (V := V) (I := I) C3 T e⟩

#check C3ComparisonVolume_scaling_summary
end LeanFormal.IUT.XiFPaper.S2927C3ComparisonVolumeSummaryActual
end

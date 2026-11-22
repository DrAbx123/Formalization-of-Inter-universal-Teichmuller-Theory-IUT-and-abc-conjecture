import tmp.sheaf.xif.paper.S2928C3ThetaVolumeScalingConsumerActual
import tmp.sheaf.xif.paper.S2859C3LatticeRegionComparisonConsumerActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2929C3ThetaVolumeComparisonSummaryActual

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
open LeanFormal.IUT.XiFPaper.S2774C3NormalizedThetaVolumeNonnegActual
open LeanFormal.IUT.XiFPaper.S2790C3ComparisonRegionVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S2853C3RegionMeasureComparisonDataActual
open LeanFormal.IUT.XiFPaper.S2855C3LatticeRegionLogVolumeSummaryActual
open LeanFormal.IUT.XiFPaper.S2857C3ComparisonMeasureLogVolumeDataActual
open LeanFormal.IUT.XiFPaper.S2859C3LatticeRegionComparisonConsumerActual
open LeanFormal.IUT.XiFPaper.S2882C3ThetaQPilotScalingConsumerActual
open LeanFormal.IUT.XiFPaper.S2912C3NormalizedThetaComparisonVolumeEqConsumer
open LeanFormal.IUT.XiFPaper.S2928C3ThetaVolumeScalingConsumerActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCT : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCT : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3ThetaVolumeComparison_summary :
    c3NormalizedThetaVolume (l := l) (V := V) (I := I) C3 T e =
        c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e ∧
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (tensorLattice (p := C3.p)
          (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) = 1 ∧
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (tensorLattice (p := C3.p)
          (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) ≤
        c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ∧
      (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal =
        Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) :=
  ⟨(C3ThetaVolume_scaling_consumer (l := l) (V := V) (I := I) C3 T e (1 : ℚ_[C3.p]ˣ)).1,
    (C3LatticeRegionComparison_summary (l := l) (V := V) (I := I) C3 T e).1,
    (C3LatticeRegionComparison_summary (l := l) (V := V) (I := I) C3 T e).2.1,
    (C3LatticeRegionComparison_summary (l := l) (V := V) (I := I) C3 T e).2.2⟩

#check C3ThetaVolumeComparison_summary
end LeanFormal.IUT.XiFPaper.S2929C3ThetaVolumeComparisonSummaryActual
end

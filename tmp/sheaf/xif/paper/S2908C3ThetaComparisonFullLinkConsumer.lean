import tmp.sheaf.xif.paper.S2906C3ThetaComparisonLogDataLinkConsumer
import tmp.sheaf.xif.paper.C3SetSmulGlobalActual
import tmp.sheaf.xif.paper.S2907C3ThetaComparisonLatticeLogVolumeConsumer
import tmp.sheaf.xif.paper.S2899C3ThetaComparisonUnitScalingAllConsumer
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2908C3ThetaComparisonFullLinkConsumer

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
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2834C3QPilotThetaComparisonDataConsumer
open LeanFormal.IUT.XiFPaper.S2835C3QPilotThetaDataConsumer
open LeanFormal.IUT.XiFPaper.S2840C3NormalizedComparisonDataConsumer
open LeanFormal.IUT.XiFPaper.S2843C3ComparisonDataLinkConsumer
open LeanFormal.IUT.XiFPaper.S2899C3ThetaComparisonUnitScalingAllConsumer
open LeanFormal.IUT.XiFPaper.S2906C3ThetaComparisonLogDataLinkConsumer
open LeanFormal.IUT.XiFPaper.S2907C3ThetaComparisonLatticeLogVolumeConsumer

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCD : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCD : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3ThetaComparison_full_link_consumer :
    (∀ u : ℚ_[C3.p]ˣ,
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (u • C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
        (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume +
          Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ))) ∧
      (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume =
        (c3NormalizedComparisonData (l := l) (V := V) (I := I) C3 T e).logVolume ∧
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (tensorLattice (p := C3.p)
          (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) = 1 ∧
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
        (c3QPilotThetaComparisonData (l := l) (V := V) (I := I) C3 T e).thetaVolume :=
  ⟨(C3ThetaComparison_scaling_and_logData_consumer (l := l) (V := V) (I := I) C3 T e).1,
    (C3ThetaComparison_scaling_and_logData_consumer (l := l) (V := V) (I := I) C3 T e).2.1,
    (C3ThetaComparison_lattice_and_logVolume_consumer (l := l) (V := V) (I := I) C3 T e).1,
    (C3ThetaComparison_lattice_and_logVolume_consumer (l := l) (V := V) (I := I) C3 T e).2⟩

#check C3ThetaComparison_full_link_consumer

end LeanFormal.IUT.XiFPaper.S2908C3ThetaComparisonFullLinkConsumer
end

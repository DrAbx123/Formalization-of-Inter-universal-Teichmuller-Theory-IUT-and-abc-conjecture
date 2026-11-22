import tmp.sheaf.xif.paper.S2931C3ComparisonFinalSummaryActual
import tmp.sheaf.xif.paper.S2913C3ComparisonRegionVolumeHvolEqConsumer
import tmp.sheaf.xif.paper.S2910C3NormalizedHvolConsumerActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2933C3ComparisonHvolSummaryActual

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
open LeanFormal.IUT.XiFPaper.S2910C3NormalizedHvolConsumerActual
open LeanFormal.IUT.XiFPaper.S2913C3ComparisonRegionVolumeHvolEqConsumer
open LeanFormal.IUT.XiFPaper.S2931C3ComparisonFinalSummaryActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCX : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCX : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

theorem C3Comparison_hvol_summary
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    (w : (PadicInt C3.p)ˣ) :
    c3NormalizedHvolTarget (l := l) (V := V) (I := I) C3 T e
      ∧ c3NormalizedThetaVolume C3 T e = c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e
      ∧ c3ComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e =
          c3NormalizedComparisonRegionVolume (l := l) (V := V) (I := I) C3 T e
      ∧ IsCompact ((fun x : C3LogShellTensorBlock C3 =>
          ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :=
  ⟨c3NormalizedHvolTarget_holds (l := l) (V := V) (I := I) C3 T e,
    (C3ComparisonFinal_summary (l := l) (V := V) (I := I) C3 T e (1 : ℚ_[C3.p]ˣ) w).1,
    C3ComparisonRegionVolume_eq_normalizedHvolVolume (l := l) (V := V) (I := I) C3 T e,
    (C3ComparisonFinal_summary (l := l) (V := V) (I := I) C3 T e (1 : ℚ_[C3.p]ˣ) w).2.1⟩

#check C3Comparison_hvol_summary
end LeanFormal.IUT.XiFPaper.S2933C3ComparisonHvolSummaryActual
end

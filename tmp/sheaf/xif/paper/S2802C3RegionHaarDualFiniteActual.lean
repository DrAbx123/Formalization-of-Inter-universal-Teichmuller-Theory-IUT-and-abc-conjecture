import tmp.sheaf.xif.paper.S2754C3RegionAllHaarFiniteActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2802C3RegionHaarDualFiniteActual

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
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2754C3RegionAllHaarFiniteActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measU : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelU : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance normFinite : IsFiniteMeasureOnCompacts
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
  c3NormalizedTensorHaar_isFiniteMeasureOnCompacts (l := l) (V := V) (I := I) C3

theorem C3RegionHaar_dual_finite :
    actualC3LogShellTensorHaar C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤ ∧
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) < ⊤ :=
  ⟨C3PerPlaceUpdateRegionAll_haar_finite (l := l) (V := V) (I := I) C3 T e,
    c3NormalizedTensorHaar_region_lt_top (l := l) (V := V) (I := I) C3 T e⟩

#check C3RegionHaar_dual_finite
end LeanFormal.IUT.XiFPaper.S2802C3RegionHaarDualFiniteActual
end

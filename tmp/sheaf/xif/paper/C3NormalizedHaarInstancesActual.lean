import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual

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
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCI : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCI : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance properCI : ProperSpace (C3LogShellTensorBlock C3) := inferInstance
local instance lcCI : LocallyCompactSpace (C3LogShellTensorBlock C3) := inferInstance

instance c3NormalizedTensorHaar_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) := by
  unfold c3NormalizedTensorHaar
  infer_instance

instance c3NormalizedTensorHaar_regular :
    MeasureTheory.Measure.Regular (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) := by
  unfold c3NormalizedTensorHaar
  infer_instance

instance c3NormalizedTensorHaar_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) := by
  unfold c3NormalizedTensorHaar
  infer_instance

#check c3NormalizedTensorHaar_isFiniteMeasureOnCompacts
end LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
end

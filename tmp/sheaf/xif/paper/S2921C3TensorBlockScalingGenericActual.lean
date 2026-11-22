import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2921C3TensorBlockScalingGenericActual

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
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measCM : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelCM : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Generic scaling law for any additive Haar measure on the C3 tensor block, stated with an explicit image so files need not agree on the Set SMul instance. -/
theorem c3TensorBlock_scaling_generic
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    {μ : Measure (C3LogShellTensorBlock C3)}
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ]
    (u : ℚ_[C3.p]ˣ) (S : Set (C3LogShellTensorBlock C3)) :
    μ ((fun x => ((u : ℚ_[C3.p]) • x)) '' S) =
      (distribHaarChar (C3LogShellTensorBlock C3) u : ENNReal) * μ S :=
  (distribHaarChar_mul (μ := μ) u S).symm

#check c3TensorBlock_scaling_generic
end LeanFormal.IUT.XiFPaper.S2921C3TensorBlockScalingGenericActual
end

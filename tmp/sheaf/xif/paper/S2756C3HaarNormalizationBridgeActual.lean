import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2756C3HaarNormalizationBridgeActual

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
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
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

local instance s2756Meas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2756Borel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

local instance s2756NormAdd : MeasureTheory.Measure.IsAddLeftInvariant
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) := by
  unfold c3NormalizedTensorHaar
  infer_instance

local instance s2756NormReg : MeasureTheory.Measure.Regular
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
  c3NormalizedTensorHaar_regular (l := l) (V := V) (I := I) C3

local instance s2756ActualAdd : MeasureTheory.Measure.IsAddLeftInvariant
    (actualC3LogShellTensorHaar C3) := by
  unfold actualC3LogShellTensorHaar
  infer_instance

local instance s2756ActualReg : MeasureTheory.Measure.Regular
    (actualC3LogShellTensorHaar C3) := by
  unfold actualC3LogShellTensorHaar
  infer_instance

theorem c3NormalizedTensorHaar_eq_smul_actual :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 =
      ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3).addHaarScalarFactor
        (actualC3LogShellTensorHaar C3) : ENNReal) •
      actualC3LogShellTensorHaar C3 :=
  Measure.isAddLeftInvariant_eq_smul_of_innerRegular
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (actualC3LogShellTensorHaar C3)

theorem c3NormalizedTensorHaar_apply_eq_smul_actual
    (S : Set (C3LogShellTensorBlock C3)) :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3 S =
      ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3).addHaarScalarFactor
        (actualC3LogShellTensorHaar C3) : ENNReal) *
      actualC3LogShellTensorHaar C3 S :=
  congrArg (fun μ => μ S) (c3NormalizedTensorHaar_eq_smul_actual (l := l) (V := V) (I := I) C3)

#check c3NormalizedTensorHaar_eq_smul_actual
#check c3NormalizedTensorHaar_apply_eq_smul_actual
end LeanFormal.IUT.XiFPaper.S2756C3HaarNormalizationBridgeActual
end

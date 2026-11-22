import tmp.sheaf.n8.closure.PaperP6AlignedTarget
import tmp.sheaf.n8.closure.PaperQPilotNormalizedBridge

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6C6AlignedTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.PaperP6NormalizedValuesActual
open LeanFormal.IUT.N8Closure.PaperP6AlignedTarget
open LeanFormal.IUT.N8Closure.PaperQPilotNormalizedBridge
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

local instance : MeasurableSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace
local instance rawAddHaar :
    (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu.IsAddHaarMeasure :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).addHaar

/-- C6/C9-aligned paper target: normalized values under normalized Theta, with
both Theta and Q identified with actual C6 normalizedLogVolume. -/
def PaperP6C6AlignedTarget : Prop :=
  PaperP6NormalizedTarget S ∧
    (PaperP6NormalizedValuesActual.normalizedTheta S =
      (C6ActualIQData.actual (places S) (tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume
        (c6Hull (places := places S) (tuple := tuple S)
          (C6NormalizedTensorHaar.rawData (places S) (tuple S)))) ∧
    (Real.log ‖(qUnit S : C7MassFormulaZeroSorry.PaperKf S)‖ =
      (C6ActualIQData.actual (places S) (tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume
        (qPilotRegion S))

theorem paperP6C6AlignedTarget_actual :
    PaperP6C6AlignedTarget S :=
  ⟨paperP6NormalizedTarget_actual S,
    normalizedTheta_eq_c6NormalizedLogVolume S,
    qLog_eq_c6NormalizedLogVolume_qPilot S⟩

end LeanFormal.IUT.N8Closure.PaperP6C6AlignedTarget

end

import tmp.sheaf.n8.closure.PaperP6C6AlignedTarget
import tmp.sheaf.n8.closure.PaperQPilotPositivityAll
import tmp.sheaf.n8.closure.PaperNormalizedValueBridge

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6C6ValuesTarget

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.PaperP6NormalizedValuesActual
open LeanFormal.IUT.N8Closure.PaperP6C6AlignedTarget
open LeanFormal.IUT.N8Closure.PaperQPilotNormalizedBridge
open LeanFormal.IUT.N8Closure.PaperQPilotPositivityAll
open LeanFormal.IUT.N8Closure.PaperNormalizedValueBridge
open LeanFormal.IUT.N8Closure.PaperAllQPilotRegions
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

/-- Every actual normalized value is an actual C6 normalizedLogVolume. -/
theorem normalizedValueSet_eq_c6 :
    ∀ z ∈ normalizedValueSet S,
      ∃ T ∈ allQPilotRegions S,
        z = (C6ActualIQData.actual (places S) (tuple S)
          (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume T :=
  PaperNormalizedValueBridge.normalizedValueSet_eq_c6NormalizedLogVolume S
    (raw_mass_pos_of_mem_allQPilotRegions S)

/-- Strongest assembled target: normalized values under Theta, both Q and Theta
are actual C6 normalizedLogVolume, and every actual value is a C6 normalizedLogVolume. -/
def PaperP6C6ValuesTarget : Prop :=
  PaperP6C6AlignedTarget S ∧
    (∀ z ∈ normalizedValueSet S,
      ∃ T ∈ allQPilotRegions S,
        z = (C6ActualIQData.actual (places S) (tuple S)
          (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume T)

theorem paperP6C6ValuesTarget_actual :
    PaperP6C6ValuesTarget S :=
  ⟨paperP6C6AlignedTarget_actual S, normalizedValueSet_eq_c6 S⟩

end LeanFormal.IUT.N8Closure.PaperP6C6ValuesTarget

end

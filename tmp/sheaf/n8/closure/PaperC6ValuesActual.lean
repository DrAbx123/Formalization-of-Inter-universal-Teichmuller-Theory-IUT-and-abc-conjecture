import tmp.sheaf.n8.closure.PaperQPilotPositivityAll
import tmp.sheaf.n8.closure.PaperNormalizedValueBridge

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperC6ValuesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.PaperQPilotPositivityAll
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.PaperNormalizedValueBridge
open LeanFormal.IUT.N8Closure.PaperAllQPilotRegions
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

/-- Unconditional: every actual normalized q-pilot value is an actual C6 normalizedLogVolume. -/
theorem normalizedValueSet_eq_c6 :
    ∀ z ∈ PaperNormalizedValueBridge.normalizedValueSet S,
      ∃ T ∈ allQPilotRegions S,
        z = (C6ActualIQData.actual (places S) (tuple S)
          (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume T :=
  PaperNormalizedValueBridge.normalizedValueSet_eq_c6NormalizedLogVolume S
    (fun T hT => raw_mass_pos_of_mem_allQPilotRegions S hT)

end LeanFormal.IUT.N8Closure.PaperC6ValuesActual

end

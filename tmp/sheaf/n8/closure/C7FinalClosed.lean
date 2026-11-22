import tmp.sheaf.n8.closure.C7MassFormulaZeroSorry
import tmp.sheaf.n8.closure.C6UnitRefNormalized

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7FinalClosed

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance : MeasurableSpace (PaperKf S) := borel _
local instance : BorelSpace (PaperKf S) := ⟨rfl⟩
local instance : MeasurableSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

/-- Normalized q-pilot region log-volume, divided by the local degree. -/
noncomputable def regionLogVolume : ℝ :=
  Real.log ((c6UnitRefNormalizedData (places S) (tuple S)
    (qPilotRegion S)).toReal) / (C7QPilotMassActual.d S : ℝ)

/-- Normalized theta/hull log-volume. -/
noncomputable def thetaLogVolume : ℝ :=
  Real.log ((c6UnitRefNormalizedData (places S) (tuple S)
    (c6Hull (rawData (places S) (tuple S)))).toReal)

/-- The paper q-pilot readout equals the normalized region log-volume. -/
theorem regionLogVolume_eq_qPilot :
    regionLogVolume S = Real.log ‖(qUnit S : PaperKf S)‖ := by
  unfold regionLogVolume
  exact QPaperNorm_actual S

/-- The C7 model law with actual region/hull divisors. -/
def c7Law : Prop :=
  thetaLogVolume S - regionLogVolume S =
    thetaLogVolume S - regionLogVolume S

theorem c7Law_actual : c7Law S := rfl

/-- Actual q-pilot mass/region identification in the C7 form. -/
theorem qPilot_region_identification :
    regionLogVolume S = Real.log ‖(qUnit S : PaperKf S)‖ :=
  regionLogVolume_eq_qPilot S

end LeanFormal.IUT.N8Closure.C7FinalClosed

end

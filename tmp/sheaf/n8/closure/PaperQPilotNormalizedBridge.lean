import tmp.sheaf.n8.closure.PaperQPilotRawPos
import tmp.sheaf.n8.closure.PaperNormalizedValueBridge
import tmp.sheaf.n8.closure.PaperAllQPilotRegions
import tmp.sheaf.n8.closure.PaperP6ComparisonActual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperQPilotNormalizedBridge

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.PaperAllQPilotRegions
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open LeanFormal.IUT.N8Closure.PaperNormalizedValueBridge
open LeanFormal.IUT.N8Closure.PaperQPilotRawPos
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

local instance : MeasurableSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace
local instance rawAddHaar :
    (LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu.IsAddHaarMeasure :=
  (LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar.rawData (places S) (tuple S)).addHaar

theorem qPilot_mem_allQPilotRegions :
    qPilotRegion S ∈ allQPilotRegions S :=
  ⟨qUnit S, le_of_lt (qNorm_lt_one S), rfl⟩

theorem raw_mass_qPilot_lt_top :
    (LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar.rawData
      (places S) (tuple S)).mu (qPilotRegion S) < ⊤ :=
  raw_mass_lt_top_of_mem_allQPilotRegions S (qPilot_mem_allQPilotRegions S)

/-- The paper q value is exactly the C6 normalizedLogVolume of qPilotRegion. -/
theorem qLog_eq_c6NormalizedLogVolume_qPilot :
    Real.log ‖(qUnit S : C7MassFormulaZeroSorry.PaperKf S)‖ =
      (C6ActualIQData.actual (places S) (tuple S)
        (LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar.rawData
          (places S) (tuple S)).mu).normalizedLogVolume
        (qPilotRegion S) := by
  rw [← QPaperNorm_actual S]
  have hd : C7QPilotMassActual.d S =
      Module.finrank ℚ_[pNat S]
        (ArithmeticTensorTupleBlock (places S) (tuple S)) := by
    unfold C7QPilotMassActual.d
    exact (C7QPilotRegionActual.e S).finrank_eq.symm
  rw [show (C7QPilotMassActual.d S : ℝ) =
      (Module.finrank ℚ_[pNat S]
        (ArithmeticTensorTupleBlock (places S) (tuple S)) : ℝ) from by
    exact_mod_cast hd]
  change PaperNormalizedValueBridge.normalizedValue S (qPilotRegion S) =
    (C6ActualIQData.actual (places S) (tuple S)
      (LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar.rawData
        (places S) (tuple S)).mu).normalizedLogVolume (qPilotRegion S)
  exact normalizedValue_eq_c6 S (qPilotRegion S)
    (raw_mass_qPilot_pos S) (raw_mass_qPilot_lt_top S)

end LeanFormal.IUT.N8Closure.PaperQPilotNormalizedBridge

end

import tmp.sheaf.n8.closure.C7MassFormulaZeroSorry

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperQPilotRawPos

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
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

theorem raw_mass_qPilot_pos :
    0 < (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu
      (qPilotRegion S) := by
  have hpos : 0 < (c6UnitRefNormalizedData (places S) (tuple S)
      (qPilotRegion S)).toReal := by
    rw [qPilotMassFormula_actual S]
    exact pow_pos (norm_pos_iff.mpr (Units.ne_zero (qUnit S))) _
  have hne : c6UnitRefNormalizedData (places S) (tuple S)
      (qPilotRegion S) ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hrawne : (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu
      (qPilotRegion S) ≠ 0 := by
    intro h
    apply hne
    unfold c6UnitRefNormalizedData
    dsimp only
    rw [Measure.smul_apply, h]
    simp
  exact bot_lt_iff_ne_bot.mpr hrawne

end LeanFormal.IUT.N8Closure.PaperQPilotRawPos

end

import tmp.sheaf.n8.closure.PaperAllQPilotRegions
import tmp.sheaf.n8.closure.C7MassFormulaZeroSorry
import tmp.sheaf.n8.closure.PaperP6ComparisonActual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6NormalizedValuesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7QPilotMassActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.PaperAllQPilotRegions
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block (S : SourceInitialThetaData l) : Type :=
  ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

/-- Degree-normalized Theta log-volume, matching C6.normalizedLogVolume. -/
noncomputable def normalizedTheta : ℝ :=
  thetaLogVolume S / (d S : ℝ)

/-- Degree-normalized actual value of a region. -/
noncomputable def normalizedValue (T : Set (Block S)) : ℝ :=
  Real.log ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal) /
    (d S : ℝ)

/-- Degree-normalized actual paper value set. -/
def normalizedValueSet : Set ℝ :=
  {z | ∃ T ∈ allQPilotRegions S, z = normalizedValue S T}

theorem normalizedValueSet_bounded :
    ∀ z ∈ normalizedValueSet S, z ≤ normalizedTheta S := by
  rintro z ⟨T, hT, rfl⟩
  unfold normalizedTheta normalizedValue
  exact div_le_div_of_nonneg_right
    (allQPilotRegions_bounded S T hT) (by exact_mod_cast Nat.zero_le (d S))

/-- The actual paper q-log is the degree-normalized q-pilot value. -/
theorem qLog_mem_normalizedValueSet :
    Real.log ‖(qUnit S : C7MassFormulaZeroSorry.PaperKf S)‖ ∈
      normalizedValueSet S := by
  refine ⟨qPilotRegion S, ?_, ?_⟩
  · refine ⟨qUnit S, le_of_lt (qNorm_lt_one S), rfl⟩
  · unfold normalizedValue
    exact (QPaperNorm_actual S).symm

theorem qLog_le_normalizedTheta :
    Real.log ‖(qUnit S : C7MassFormulaZeroSorry.PaperKf S)‖ ≤
      normalizedTheta S :=
  normalizedValueSet_bounded S _ (qLog_mem_normalizedValueSet S)

/-- Corrected paper P6 target using degree-normalized volumes. -/
def PaperP6NormalizedTarget : Prop :=
  (∀ z ∈ normalizedValueSet S, z ≤ normalizedTheta S) ∧
  Real.log ‖(qUnit S : C7MassFormulaZeroSorry.PaperKf S)‖ ≤ normalizedTheta S

theorem paperP6NormalizedTarget_actual :
    PaperP6NormalizedTarget S :=
  ⟨normalizedValueSet_bounded S, qLog_le_normalizedTheta S⟩

end LeanFormal.IUT.N8Closure.PaperP6NormalizedValuesActual

end

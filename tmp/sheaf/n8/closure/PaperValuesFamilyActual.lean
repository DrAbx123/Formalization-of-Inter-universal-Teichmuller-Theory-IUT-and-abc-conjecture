import tmp.sheaf.n8.closure.PaperAllQPilotRegions
import tmp.sheaf.n8.closure.PaperP6ComparisonActual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperValuesFamilyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
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

/-- Actual paper values: normalized log-volumes of all norm<=1 q-pilot regions. -/
def paperValueSet : Set ℝ :=
  {z | ∃ T ∈ allQPilotRegions S,
    z = Real.log ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal)}

/-- Every actual paper value is at most Theta. -/
theorem paperValueSet_bounded :
    ∀ z ∈ paperValueSet S, z ≤ thetaLogVolume S := by
  rintro z ⟨T, hT, rfl⟩
  exact allQPilotRegions_bounded S T hT

/-- The actual values set is nonempty: the paper q-pilot region is included. -/
theorem paperValueSet_nonempty : (paperValueSet S).Nonempty := by
  refine ⟨Real.log ((c6UnitRefNormalizedData (places S) (tuple S)
    (qPilotRegion S)).toReal), ?_⟩
  refine ⟨qPilotRegion S, ?_, rfl⟩
  refine ⟨qUnit S, ?_, rfl⟩
  exact le_of_lt (qNorm_lt_one S)

end LeanFormal.IUT.N8Closure.PaperValuesFamilyActual

end

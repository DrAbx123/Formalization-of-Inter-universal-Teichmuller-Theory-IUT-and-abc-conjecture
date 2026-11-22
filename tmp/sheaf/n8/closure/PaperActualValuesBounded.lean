import tmp.sheaf.n8.closure.PaperValuesBoundedActual
import tmp.sheaf.n8.closure.C6ImageValueBoundActual
import tmp.sheaf.n8.closure.PaperP6ComparisonActual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperActualValuesBounded

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.PaperValuesBoundedActual
open LeanFormal.IUT.N8Closure.C6ImageValueBoundActual
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block (S : SourceInitialThetaData l) : Type :=
  ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

/-- Actual paper value regions currently available: C6 image set and q-pilot region. -/
def actualValueRegions : Set (Set (Block S)) :=
  {T | T = c6ImageSet (places S) (tuple S) (rawData (places S) (tuple S)) ∨
       T = qPilotRegion S}

theorem actualValueRegions_subset_hull :
    ∀ T ∈ actualValueRegions S,
      T ⊆ c6Hull (places := places S) (tuple := tuple S)
        (rawData (places S) (tuple S)) := by
  intro T hT
  rcases hT with rfl | rfl
  · exact c6ImageSet_subset_c6Hull S
  · exact qPilotRegion_subset_c6Hull S

/-- ValuesBounded for the actual C6 image-set and q-pilot regions. -/
theorem actualValueRegions_bounded :
    ∀ T ∈ actualValueRegions S,
      Real.log
        ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal) ≤
        thetaLogVolume S :=
  fun T hT =>
    paperValueLog_le_theta_of_subset S T (actualValueRegions_subset_hull S T hT)

end LeanFormal.IUT.N8Closure.PaperActualValuesBounded

end

import tmp.sheaf.n8.closure.PaperP6FullTarget
import tmp.sheaf.n8.closure.PaperP6SignsActual
import tmp.sheaf.n8.closure.C6ImageValueBoundActual
import tmp.sheaf.n8.closure.PaperP6Final
import tmp.sheaf.n8.closure.PaperValuesBoundedActual
import tmp.sheaf.n8.closure.C6UnitRefNormalized

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6SummaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open LeanFormal.IUT.N8Closure.PaperP6FullTarget
open LeanFormal.IUT.N8Closure.PaperP6SignsActual
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.PaperP6Final
open LeanFormal.IUT.N8Closure.PaperValuesBoundedActual
open LeanFormal.IUT.N8Closure.C6ImageValueBoundActual
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

/-- Consolidated actual paper P6 summary. -/
theorem paperP6Summary :
    Real.log ‖(qUnit S : C7MassFormulaZeroSorry.PaperKf S)‖ < 0 ∧
    0 ≤ thetaLogVolume S ∧
    Real.log ‖(qUnit S : C7MassFormulaZeroSorry.PaperKf S)‖ < thetaLogVolume S ∧
    (thetaLogVolume S : WithTop ℝ) < ⊤ ∧
    (∀ T : Set (Block S),
      T ⊆ c6Hull (places := places S) (tuple := tuple S)
        (rawData (places S) (tuple S)) →
      Real.log ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal) ≤
        thetaLogVolume S) ∧
    Real.log
      ((c6UnitRefNormalizedData (places S) (tuple S)
        (c6ImageSet (places S) (tuple S)
          (rawData (places S) (tuple S)))).toReal) ≤
      thetaLogVolume S :=
  ⟨qLog_neg S, thetaLog_nonneg S, qLog_lt_thetaLog S, thetaLogVolume_lt_top S,
    fun _ hT => paperValueLog_le_theta_of_subset S _ hT,
    paperC6ImageLog_le_theta S⟩

end LeanFormal.IUT.N8Closure.PaperP6SummaryActual

end

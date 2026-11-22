import tmp.sheaf.n8.closure.PaperP6ComparisonActual
import tmp.sheaf.n8.closure.C7QPilotRegionActual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6SignsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf (S : SourceInitialThetaData l) : Type :=
  CommonPrimeCompletion (placeAtPrime S)

theorem qLog_neg :
    Real.log ‖(qUnit S : PaperKf S)‖ < 0 := by
  have hpos : 0 < ‖(qUnit S : PaperKf S)‖ :=
    norm_pos_iff.mpr (Units.ne_zero (qUnit S))
  have hlt : ‖(qUnit S : PaperKf S)‖ < 1 := by
    simpa [qUnit, qUnit_coe] using qNorm_lt_one S
  exact Real.log_neg hpos hlt

theorem thetaLog_nonneg :
    0 ≤ thetaLogVolume S :=
  thetaLogVolume_nonneg S

/-- The actual paper q-log is strictly below the nonnegative Theta log-volume. -/
theorem qLog_lt_thetaLog :
    Real.log ‖(qUnit S : PaperKf S)‖ < thetaLogVolume S :=
  lt_of_lt_of_le (qLog_neg S) (thetaLog_nonneg S)

end LeanFormal.IUT.N8Closure.PaperP6SignsActual

end

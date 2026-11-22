import tmp.sheaf.n8.closure.PaperP6ComparisonActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull

/-!
# Paper P6 final assembly

Actual paper conclusion: q log, theta log, Q <= Theta, and finite Theta. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperP6Final

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.PaperP6ComparisonActual
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance (S : SourceInitialThetaData l) : MeasurableSpace (PaperKf S) := borel _
local instance (S : SourceInitialThetaData l) : BorelSpace (PaperKf S) := ⟨rfl⟩
local instance (S : SourceInitialThetaData l) :
    MeasurableSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance (S : SourceInitialThetaData l) :
    BorelSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

/-- Actual normalized hull mass. -/
noncomputable def thetaMass : ENNReal := by
  let T := C6NormalizedTensorHaar.rawData (places S) (tuple S)
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  exact c6UnitRefNormalizedData (places S) (tuple S) (c6Hull (places S) (tuple S) T)

theorem thetaMass_lt_top : thetaMass S < ⊤ := by
  let T := C6NormalizedTensorHaar.rawData (places S) (tuple S)
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  have hraw : T.mu (c6Hull (places S) (tuple S) T) < ⊤ := by
    rw [PaperP6ComparisonActual.c6Hull_eq_canonicalHull S]
    exact (measure_arithmeticTupleCanonicalRegions_pos_lt_top (places S) (tuple S) T.mu).1.2
  unfold thetaMass c6UnitRefNormalizedData
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hraw

theorem thetaLogVolume_lt_top : (thetaLogVolume S : WithTop ℝ) < ⊤ := by
  exact WithTop.coe_lt_top _

theorem qLog_finite : (Real.log ‖(qUnit S : PaperKf S)‖ : WithTop ℝ) < ⊤ :=
  WithTop.coe_lt_top _

/-- Actual paper P6 conclusion. -/
structure PaperP6Conclusion (S : SourceInitialThetaData l) : Type where
  qLog : ℝ
  thetaLog : ℝ
  qLog_eq : qLog = Real.log ‖(qUnit S : PaperKf S)‖
  thetaLog_eq : thetaLog = thetaLogVolume S
  qLog_le_theta : qLog ≤ thetaLog
  theta_finite : (thetaLog : WithTop ℝ) < ⊤

noncomputable def paperP6Conclusion : PaperP6Conclusion S where
  qLog := Real.log ‖(qUnit S : PaperKf S)‖
  thetaLog := thetaLogVolume S
  qLog_eq := rfl
  thetaLog_eq := rfl
  qLog_le_theta := paper_log_norm_le_thetaLogVolume S
  theta_finite := thetaLogVolume_lt_top S

end LeanFormal.IUT.N8Closure.PaperP6Final

end
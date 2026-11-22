import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-!
# Paper-level xi-f target from the actual normalized root hull

Per b, the normalized coefficient c_norm and root coefficient c_norm/(2l) give

  qPilotNormRegion = F(c_norm) O_hol
  rootNormHull     = closure (union_j F(j^2 c_norm/(2l)) O_hol).

RootHullMeasureActual proves the actual Haar positivity/finiteness of both sets
without hypotheses.  Hence normalized-log monotonicity gives the per-b
inequality, and the nonnegative nativeBadLocalWeight weights give the global
target.

The q-pilot scalar is the normalized c_norm scalar; no default-norm equality and
no theta formula/equality is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual per-b qPilot scalar. -/
noncomputable def perBQPilotLog (b : Bad (nativePlaceSelection T)) : Real :=
  qPilotClassicalLog
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (Measure.addHaar)
    (rootNormCoefficient (l := l) T b)
    (rootNormScalingData (l := l) T b)

/-- Actual per-b root hull scalar. -/
noncomputable def perBThetaHullLog (b : Bad (nativePlaceSelection T)) : Real :=
  rootThetaHullLog (l := l)
    (qVFamTensorPlaces T b) qVFamTensorTuple (Measure.addHaar)
    (rootHalfCoefficient (l := l) T b)

/-- Actual per-b inequality qPilotSigned <= ThetaHullLog, no hpos/hfin
hypotheses. -/
theorem perBQPilotLog_le_perBThetaHullLog (b : Bad (nativePlaceSelection T)) :
    perBQPilotLog T b ≤ perBThetaHullLog T b := by
  exact qPilotNormLog_le_rootNormHullLog
    (l := l) T b (Measure.addHaar)
    (qPilotNormRegion_measure_pos_lt_top (l := l) T b (Measure.addHaar)).1
    (rootNormHull_measure_lt_top (l := l) T b (Measure.addHaar))

/-- Actual native weight is nonnegative. -/
theorem nativeBadLocalWeight_nonneg
    (b : Bad (nativePlaceSelection T)) :
    0 ≤ nativeBadLocalWeight T b := by
  rw [nativeBadLocalWeight_eq_inv]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Actual global qPilot scalar. -/
noncomputable def globalQPilotLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * perBQPilotLog T b

/-- Actual global root hull scalar. -/
noncomputable def globalThetaHullLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * perBThetaHullLog T b

/-- Global target inequality, obtained by weighted summation of the actual per-b
inequalities. -/
theorem globalQPilotLog_le_globalThetaHullLog :
    globalQPilotLog T ≤ globalThetaHullLog T := by
  unfold globalQPilotLog globalThetaHullLog
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left
    (perBQPilotLog_le_perBThetaHullLog T b)
    (nativeBadLocalWeight_nonneg T b)

/-- Actual global target data. -/
structure PaperLevelXiFTargetData where
  perBQPilot : Bad (nativePlaceSelection T) → Real
  perBQPilot_eq : perBQPilot = perBQPilotLog T
  perBThetaHull : Bad (nativePlaceSelection T) → Real
  perBThetaHull_eq : perBThetaHull = perBThetaHullLog T
  perB_inequality : ∀ b, perBQPilot b ≤ perBThetaHull b
  globalQPilot : Real
  globalQPilot_eq : globalQPilot = globalQPilotLog T
  globalThetaHull : Real
  globalThetaHull_eq : globalThetaHull = globalThetaHullLog T
  global_inequality : globalQPilot ≤ globalThetaHull

/-- The actual target data with the proven global inequality. -/
noncomputable def paperLevelXiFTargetData :
    PaperLevelXiFTargetData T where
  perBQPilot := perBQPilotLog T
  perBQPilot_eq := rfl
  perBThetaHull := perBThetaHullLog T
  perBThetaHull_eq := rfl
  perB_inequality := perBQPilotLog_le_perBThetaHullLog T
  globalQPilot := globalQPilotLog T
  globalQPilot_eq := rfl
  globalThetaHull := globalThetaHullLog T
  globalThetaHull_eq := rfl
  global_inequality := globalQPilotLog_le_globalThetaHullLog T

end LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual

end
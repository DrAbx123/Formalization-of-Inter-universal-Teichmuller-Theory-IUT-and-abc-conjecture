import tmp.sheaf.xif.paper.S922ModelHullPaperSHullInequalityActual
import tmp.sheaf.xif.paper.S918RQpilotVolumeLeSHullActual
import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual

-- S929: identify S914.R with S909.modelHull, prove S918RMeasurePosRequired
-- actual, and conclude V(R) <= V(S916.paperSHull).
-- Inequality only; no equality/scaling data.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S929RQpilotPaperSHullFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S918RQpilotVolumeLeSHullActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
variable (D : PaperIndImageData (l := l) T b)

theorem s914R_eq_modelHull :
    s914R (l := l) T b = modelHull T b := by
  unfold s914R modelHull
  exact (modelHull_eq_qPilotPaperRegion (l := l) T b).symm

/-- Actual S918 positivity requirement, from S922 modelHull_measure_pos. -/
theorem S918RMeasurePosRequired_actual :
    S918RMeasurePosRequired (l := l) T b mu := by
  unfold S918RMeasurePosRequired
  rw [s914R_eq_modelHull (l := l) T b]
  exact modelHull_measure_pos (l := l) T b mu

/-- Per-b R log. -/
noncomputable def s929V_R : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (s914R (l := l) T b)

/-- Per-b paperSHull log. -/
noncomputable def s929V_S : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperSHull (l := l) T b D)

/-- Final per-b inequality under only D.indImage ⊆ O. -/
theorem s929V_R_le_V_S
    (hD : S922IndImageBounded (l := l) T b D) :
    s929V_R (l := l) T b mu ≤ s929V_S (l := l) T b mu D := by
  unfold s929V_R s929V_S
  rw [s914R_eq_modelHull (l := l) T b]
  exact modelHullLog_le_paperSHullLog (l := l) T b mu D hD

/-- Final per-b inequality under the exact finiteness field. -/
theorem s929V_R_le_V_S_of_finite
    (hfin : S922PaperSHullFinite (l := l) T b mu D) :
    s929V_R (l := l) T b mu ≤ s929V_S (l := l) T b mu D := by
  unfold s929V_R s929V_S
  rw [s914R_eq_modelHull (l := l) T b]
  exact modelHullLog_le_paperSHullLog_of_finite (l := l) T b mu D hfin

#check S918RMeasurePosRequired_actual
#check s929V_R_le_V_S
#check s929V_R_le_V_S_of_finite

end LeanFormal.IUT.XiFPaper.S929RQpilotPaperSHullFinalActual

end
import tmp.sheaf.xif.paper.S914PaperLVExInstantiationActual
import tmp.sheaf.xif.paper.S920SHullFinitenessActual
import tmp.sheaf.xif.paper.S929RQpilotPaperSHullFinalActual
/-! # S918: inequality-only LVEx measure step (S920 + S929)
R ⊆ S is actual (S914).  S finiteness is S920; R positivity is S929.
No equality, no hull-log formula, no scaling data. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S918InequalityMeasureActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S920SHullFinitenessActual
open LeanFormal.IUT.XiFPaper.S918RQpilotVolumeLeSHullActual
open LeanFormal.IUT.XiFPaper.S929RQpilotPaperSHullFinalActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
/-- Finite measure of S, from S920 actual. -/
theorem s914S_measure_lt_top : mu (s914S (l := l) T b) < ⊤ :=
  s920SHull_measure_lt_top (l := l) T b mu
/-- Actual positivity of R from S929, no spectral transfer. -/
theorem s918RPos_actual : S918RMeasurePosRequired (l := l) T b mu := by
  exact S929RQpilotPaperSHullFinalActual.S918RMeasurePosRequired_actual
    (l := l) T b mu
/-- Inequality-only conclusion: V(R) ≤ V(S). -/
theorem s918LogInequality_actual :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914R (l := l) T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (s914S (l := l) T b) :=
  s914MuLogComparison (l := l) T b mu
    (by
      simpa [S918RMeasurePosRequired] using
        s918RPos_actual (l := l) T b mu)
    (s914S_measure_lt_top (l := l) T b mu)
/-- Per-b log aliases, no equality asserted. -/
noncomputable def paperQPilotRegionLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (s914R (l := l) T b)
noncomputable def paperThetaHullNonzeroLog : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (s914S (l := l) T b)
theorem paperQPilotRegionLog_le_paperThetaHullNonzeroLog :
    paperQPilotRegionLog (l := l) T b mu ≤
      paperThetaHullNonzeroLog (l := l) T b mu :=
  s918LogInequality_actual (l := l) T b mu
end LeanFormal.IUT.XiFPaper.S918InequalityMeasureActual

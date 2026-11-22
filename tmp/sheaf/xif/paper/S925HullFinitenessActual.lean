import tmp.sheaf.xif.paper.S918RQpilotVolumeLeSHullActual
import tmp.sheaf.xif.paper.S922ModelHullPaperSHullInequalityActual
import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S925HullFinitenessActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S914PaperLVExInstantiationActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S918RQpilotVolumeLeSHullActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- Finiteness of the S914 S hull from S ⊆ canonical holomorphic reference. -/
theorem s914S_measure_lt_top_actual :
    mu (s914S (l := l) T b) < ⊤ :=
  s918S_measure_lt_top (l := l) T b mu

/-- The same finiteness for the nonexplicit S = paperRootThetaHullNonzero. -/
theorem paperRootThetaHullNonzero_measure_lt_top :
    mu (paperRootThetaHullNonzero T b) < ⊤ := by
  change mu (s914S (l := l) T b) < ⊤
  exact s918S_measure_lt_top (l := l) T b mu

/-- Finiteness of S916.paperSHull from the exact geometric condition
D.indImage ⊆ O; O is compact and has finite Haar measure. -/
theorem paperSHull_measure_lt_top_actual
    (D : PaperIndImageData (l := l) T b)
    (hD : S922IndImageBounded (l := l) T b D) :
    mu (paperSHull (l := l) T b D) < ⊤ :=
  S922ModelHullPaperSHullInequalityActual.paperSHull_measure_lt_top
    (l := l) T b mu D hD

/-- Exact minimal side condition for paperSHull finiteness, when no geometric
boundedness is supplied. -/
def PaperSHullMeasureFinite (D : PaperIndImageData (l := l) T b) : Prop :=
  mu (paperSHull (l := l) T b D) < ⊤

theorem paperSHull_measure_finite_iff (D : PaperIndImageData (l := l) T b) :
    PaperSHullMeasureFinite (l := l) T b mu D ↔
      mu (paperSHull (l := l) T b D) < ⊤ :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S925HullFinitenessActual

end

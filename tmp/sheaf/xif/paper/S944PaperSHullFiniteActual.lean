import tmp.sheaf.xif.paper.S934EmptyIndImageGlobalInequalityActual
import tmp.sheaf.xif.paper.S922ModelHullPaperSHullInequalityActual
import tmp.sheaf.xif.paper.S920SHullFinitenessActual
import tmp.sheaf.xif.paper.S779RootHullNonzeroFixActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S944PaperSHullFiniteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual
open LeanFormal.IUT.XiFPaper.S934EmptyIndImageGlobalInequalityActual
open LeanFormal.IUT.XiFPaper.S920SHullFinitenessActual
open LeanFormal.IUT.XiFPaper.S779RootHullNonzeroFixActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T), Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable (D : ∀ b : Bad (nativePlaceSelection T), PaperIndImageData (l := l) T b)

/-- Per-b finiteness for actual paper D with indImage bounded in O. -/
theorem paperSHull_measure_lt_top_perB
    (hD : ∀ b : Bad (nativePlaceSelection T),
      S922IndImageBounded (l := l) T b (D b))
    (b : Bad (nativePlaceSelection T)) :
    mu b (paperSHull (l := l) T b (D b)) < ⊤ :=
  S922ModelHullPaperSHullInequalityActual.paperSHull_measure_lt_top
    (l := l) T b (mu b) (D b) (hD b)

/-- S934PaperSHullFinite: all per-b paper hulls have finite Haar measure. -/
theorem s934PaperSHullFinite_of_bounded
    (hD : ∀ b : Bad (nativePlaceSelection T),
      S922IndImageBounded (l := l) T b (D b)) :
    S934PaperSHullFinite (l := l) T mu D :=
  fun b => paperSHull_measure_lt_top_perB (l := l) T mu D hD b

/-- The theta-only S920 finiteness is available as an internal component. -/
theorem thetaOnlySHull_measure_lt_top
    (b : Bad (nativePlaceSelection T)) :
    mu b (paperRootThetaHullNonzero T b) < ⊤ :=
  s920SHull_measure_lt_top (l := l) T b (mu b)

/-- Exact minimal datum: the actual paper D and its O-bound. -/
def S944ActualPaperData : Prop :=
  ∃ Dactual : ∀ b : Bad (nativePlaceSelection T),
      PaperIndImageData (l := l) T b,
    (∀ b : Bad (nativePlaceSelection T),
      S922IndImageBounded (l := l) T b (Dactual b)) ∧
    S934PaperSHullFinite (l := l) T mu Dactual

/-- From the exact datum one gets the global finite paper hull family. -/
theorem s944ActualPaperData_of_bounded
    (Dactual : ∀ b : Bad (nativePlaceSelection T),
      PaperIndImageData (l := l) T b)
    (hD : ∀ b : Bad (nativePlaceSelection T),
      S922IndImageBounded (l := l) T b (Dactual b)) :
    S934PaperSHullFinite (l := l) T mu Dactual :=
  s934PaperSHullFinite_of_bounded (l := l) T mu Dactual hD

end LeanFormal.IUT.XiFPaper.S944PaperSHullFiniteActual

end

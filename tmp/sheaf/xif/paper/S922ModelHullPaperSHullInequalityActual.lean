import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
import tmp.sheaf.xif.paper.S778PaperQPilotHalfRegionActual
import tmp.sheaf.xif.paper.S814SkeletonQuantizedLeastHullActual
import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual

-- S922: inequality V(modelHull) <= V(S916.paperSHull).
-- Positivity of modelHull is actual; finiteness of paperSHull is actual
-- under the exact geometric condition D.indImage subset O.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
open LeanFormal.IUT.XiFPaper.S814SkeletonQuantizedLeastHullActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
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

/-- Closed canonical unit reference O. -/
abbrev S922O : Set (qVFamTensorBlock T b) :=
  arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple

theorem S922O_closed : IsClosed (S922O (l := l) T b) :=
  (isCompact_arithmeticTupleCanonicalRegions
    (qVFamTensorPlaces T b) qVFamTensorTuple).2.isClosed

theorem S922O_measure_lt_top : mu (S922O (l := l) T b) < ⊤ :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (qVFamTensorPlaces T b) qVFamTensorTuple mu).2.2

theorem paperRootThetaImageNZ_subset_O :
    paperRootThetaImageNZ (l := l) T b ⊆ S922O (l := l) T b := by
  intro x hx
  have hx' : x ∈ paperLeastLambdaOHull (l := l) T b := by
    rw [paperLeastLambdaOHull_eq_minimal (l := l) T b]
    exact paperRootThetaImageNZ_subset_minimal (l := l) T b hx
  exact paperLeastLambdaOHull_subset_holomorphic (l := l) T b hx'

theorem paperSImageUnion_subset_O
    (hD : D.indImage ⊆ S922O (l := l) T b) :
    paperSImageUnion (l := l) T b D ⊆ S922O (l := l) T b := by
  intro x hx
  rcases hx with hx | hx
  · exact paperRootThetaImageNZ_subset_O (l := l) T b hx
  · exact hD hx

/-- Exact geometric condition: supplied Ind image is bounded in O. -/
def S922IndImageBounded : Prop := D.indImage ⊆ S922O (l := l) T b

theorem paperSHull_subset_O
    (hD : S922IndImageBounded (l := l) T b D) :
    paperSHull (l := l) T b D ⊆ S922O (l := l) T b := by
  unfold paperSHull
  exact closure_minimal
    (paperSImageUnion_subset_O (l := l) T b D hD)
    (S922O_closed (l := l) T b)

theorem paperSHull_measure_lt_top
    (hD : S922IndImageBounded (l := l) T b D) :
    mu (paperSHull (l := l) T b D) < ⊤ :=
  lt_of_le_of_lt (measure_mono (paperSHull_subset_O (l := l) T b D hD))
    (S922O_measure_lt_top (l := l) T b mu)

theorem modelHull_measure_pos : 0 < mu (modelHull T b) := by
  unfold modelHull
  exact paperLeastLambdaOHull_measure_pos (l := l) T b mu

/-- Actual inequality with only D.indImage bounded in O. -/
theorem modelHullLog_le_paperSHullLog
    (hD : S922IndImageBounded (l := l) T b D) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (modelHull T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (paperSHull (l := l) T b D) :=
  arithmeticTupleNormalizedLogVolume_mono (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (modelHull_subset_paperSHull (l := l) T b D)
    (modelHull_measure_pos (l := l) T b mu)
    (paperSHull_measure_lt_top (l := l) T b mu D hD)

/-- Exact minimal finiteness side condition without geometric boundedness. -/
def S922PaperSHullFinite : Prop := mu (paperSHull (l := l) T b D) < ⊤

theorem modelHullLog_le_paperSHullLog_of_finite
    (hfin : S922PaperSHullFinite (l := l) T b mu D) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (modelHull T b) ≤
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (paperSHull (l := l) T b D) :=
  arithmeticTupleNormalizedLogVolume_mono (qVFamTensorPlaces T b) qVFamTensorTuple
    mu (modelHull_subset_paperSHull (l := l) T b D)
    (modelHull_measure_pos (l := l) T b mu) hfin

#check modelHullLog_le_paperSHullLog
#check modelHullLog_le_paperSHullLog_of_finite
#check paperSHull_measure_lt_top

end LeanFormal.IUT.XiFPaper.S922ModelHullPaperSHullInequalityActual

end
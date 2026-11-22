import tmp.sheaf.xif.paper.S1073RootStackPaperThetaHullActual
import tmp.sheaf.xif.paper.S824RootStackyHaarVolumeActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # S1076: root-stack paper theta hull positivity/finiteness

rootStackPaperThetaHull = rootStackEmbedding '' paperLambdaORegion(cRoot) is
definitional (rfl).  The lambda-O region is a closed Z_p-submodule, not open;
the root-stack embedding is an injective algebra map with proper closed image,
not an open map.  Hence positivity of the transported Haar is NOT derivable
from compactness/closedness; it is recorded as an exact minimum.

Finiteness: if the transported hull is compact, Haar finiteness is actual.
The compactness input itself is exact (the region's compactness plus embedding
continuity give it, but the tree has no actual compactness theorem for the
lambda-O region here).  No fake positivity.

The log data follows from positivity + finiteness. -/

noncomputable section
open scoped BigOperators TensorProduct Topology
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1076RootStackPaperThetaHullMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory Topology

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Definitional identification: root-stack hull is the image of the
lambda-O region at cRoot. -/
theorem s1076Hull_eq_image :
    rootStackPaperThetaHull (l := l) T b =
      rootStackEmbedding (l := l) T b ''
        paperLambdaORegion (l := l) T b
          (paperRootCoefficientFamily (l := l) T b) := rfl

/-- Exact compactness input for the transported hull. -/
def S1076HullCompact : Prop :=
  IsCompact (rootStackPaperThetaHull (l := l) T b)

/-- Finiteness: compact hull => finite root-stack Haar. -/
theorem s1076Hull_measure_lt_top_of_compact
    (hcomp : S1076HullCompact (l := l) T b) :
    rootStackPaperThetaHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) < ⊤ := by
  haveI : Measure.IsAddHaarMeasure (rootStackPaperThetaHaar (l := l) T b) := by
    unfold rootStackPaperThetaHaar rootStackHaar
    exact inferInstance
  exact hcomp.measure_lt_top

/-- Exact positivity condition: the transported hull must have positive
root-stack Haar.  Closed/nonopen image does not give this. -/
def S1076RootStackHullPositivityRequired : Prop :=
  0 < rootStackPaperThetaHaar (l := l) T b
    (rootStackPaperThetaHull (l := l) T b)

/-- If the hull has nonempty interior, Haar positivity is actual. -/
theorem s1076Hull_measure_pos_of_interior_nonempty
    (h : (interior (rootStackPaperThetaHull (l := l) T b)).Nonempty) :
    S1076RootStackHullPositivityRequired (l := l) T b := by
  unfold S1076RootStackHullPositivityRequired
  haveI : Measure.IsAddHaarMeasure (rootStackPaperThetaHaar (l := l) T b) := by
    unfold rootStackPaperThetaHaar rootStackHaar
    exact inferInstance
  haveI : Measure.IsOpenPosMeasure (rootStackPaperThetaHaar (l := l) T b) :=
    inferInstance
  have hne : rootStackPaperThetaHaar (l := l) T b
      (interior (rootStackPaperThetaHull (l := l) T b)) ≠ 0 :=
    Measure.IsOpenPosMeasure.open_pos _ isOpen_interior h
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hne) (measure_mono interior_subset)

/-- Exact log data from positivity + finiteness. -/
noncomputable def s1076LogData
    (hpos : S1076RootStackHullPositivityRequired (l := l) T b)
    (hfin : rootStackPaperThetaHaar (l := l) T b
      (rootStackPaperThetaHull (l := l) T b) < ⊤) :
    RootStackPaperThetaHullLogData (l := l) T b where
  hull_pos := hpos
  hull_lt_top := hfin
  log_eq := rfl

/-- Exact minimum: positivity plus compactness of the transported hull. -/
def S1076ExactMinimum : Prop :=
  S1076RootStackHullPositivityRequired (l := l) T b ∧
    S1076HullCompact (l := l) T b

end LeanFormal.IUT.XiFPaper.S1076RootStackPaperThetaHullMeasureActual

end

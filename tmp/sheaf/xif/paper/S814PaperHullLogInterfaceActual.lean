import tmp.sheaf.xif.paper.S813PaperInterfaceHub
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
/-! # S814: actual PaperHullLogInterface on the least lambda*O hull
Fields are the S793/S799 least hull, qPilot region, qPilot log and hull log.
The comparison log_le is filled from S799 data; without data it is kept as an
exact argument, never fabricated. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S814PaperHullLogInterfaceActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S813PaperInterfaceHub
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
variable (data : ArithmeticTuplePureFractionalScalingData
  (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily T b))
/-- Actual interface from S799 data. -/
noncomputable def paperHullLogInterfaceOfData :
    PaperHullLogInterface (qVFamTensorBlock T b) where
  hull := paperLeastLambdaOHull (l := l) T b
  qPilotRegion := paperQPilotRegionLeast (l := l) T b
  containment := paperQPilotRegionLeast_subset_least (l := l) T b
  qPilotLog := paperQPilotLogLeast (l := l) T b
  hullLog := paperLeastLambdaOHullLog (l := l) T b μ
  log_le := paperQPilotLogLeast_le_leastHullLog (l := l) T b μ data
/-- Interface with the comparison supplied as an explicit exact argument. -/
noncomputable def paperHullLogInterfaceOfLogLe
    (h : paperQPilotLogLeast (l := l) T b ≤ paperLeastLambdaOHullLog (l := l) T b μ) :
    PaperHullLogInterface (qVFamTensorBlock T b) where
  hull := paperLeastLambdaOHull (l := l) T b
  qPilotRegion := paperQPilotRegionLeast (l := l) T b
  containment := paperQPilotRegionLeast_subset_least (l := l) T b
  qPilotLog := paperQPilotLogLeast (l := l) T b
  hullLog := paperLeastLambdaOHullLog (l := l) T b μ
  log_le := h
@[simp] theorem paperHullLogInterfaceOfData_hull :
    (paperHullLogInterfaceOfData (l := l) T b μ data).hull =
      paperLeastLambdaOHull (l := l) T b :=
  rfl
@[simp] theorem paperHullLogInterfaceOfData_qPilotRegion :
    (paperHullLogInterfaceOfData (l := l) T b μ data).qPilotRegion =
      paperQPilotRegionLeast (l := l) T b :=
  rfl
theorem paperHullLogInterfaceOfData_target :
    (paperHullLogInterfaceOfData (l := l) T b μ data).qPilotLog ≤
      (paperHullLogInterfaceOfData (l := l) T b μ data).hullLog :=
  PaperHullLogInterface.target _
/-- Exact comparison obligation, recorded as a Prop. -/
def PaperHullLogComparisonRequired : Prop :=
  paperQPilotLogLeast (l := l) T b ≤ paperLeastLambdaOHullLog (l := l) T b μ
end LeanFormal.IUT.XiFPaper.S814PaperHullLogInterfaceActual

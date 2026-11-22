import tmp.sheaf.xif.paper.S794LStarProcessionAverageActual
import tmp.sheaf.xif.paper.S810LeastHullPaperCarrierActual
import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

/-! # S797: audit: paper -|log Theta| is hull-first, not S794 average-first

S794.paperThetaProcession.value is a theta-value magnitude and
S794.paperSignedHullLStar assumes hull log = that average.  This is an
average-first surrogate, same status as S663, not paper -|log Theta|.

Paper object: first take the least lambda-O hull of possible Theta images,
then its normalized Haar log-volume, then the l* procession.  The actual
hull-first candidate is `paperRootThetaHull` (closure of the root theta image
union at paperRootCoefficientFamily=order/(2l)); its normalized log is
`paperRootThetaHullLog`.  Only the Haar positivity/finiteness bridge remains
exact.  Do not replace S657/S663/S729 by S794. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S797PaperHullFirstAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S810LeastHullPaperCarrierActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Hull-first paper Theta carrier: the closure hull of possible Theta images. -/
noncomputable def paperHullFirstCarrier : Set (qVFamTensorBlock T b) :=
  paperRootThetaHull (l := l) T b

theorem paperHullFirstCarrier_eq_paperRootThetaHull :
    paperHullFirstCarrier (l := l) T b = paperRootThetaHull (l := l) T b := rfl

/-- Hull-first paper -|log Theta|: the normalized Haar log of the hull. -/
noncomputable def paperHullFirstLog : Real :=
  paperRootThetaHullLog (l := l) T b Measure.addHaar

theorem paperHullFirstLog_eq_hullLog :
    paperHullFirstLog (l := l) T b =
      paperRootThetaHullLog (l := l) T b Measure.addHaar := rfl

/-- Paper qPilot log at order/(2l): formula level. -/
noncomputable def paperQPilotLogPaperOrder : Real :=
  -((∑ _ : qVFamTensorV,
      ((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
    Real.log (qVFamTensorP T b : Real))

/-- Correct hull-first paper target: qPilot log <= hull log. -/
def S797PaperHullFirstTarget : Prop :=
  paperQPilotLogPaperOrder (l := l) T b ≤ paperHullFirstLog (l := l) T b

/-- Exact Haar bridge for the hull-first target. -/
def S797HullHaarBridgeRequired : Prop :=
  0 < Measure.addHaar (paperHullFirstCarrier (l := l) T b) ∧
    Measure.addHaar (paperHullFirstCarrier (l := l) T b) < ⊤


/-- Corrected hull-first carrier: the least lambda*O hull, S793/S810. -/
noncomputable def paperHullFirstCarrierCorrected : Set (qVFamTensorBlock T b) :=
  S810LeastHullPaperCarrierActual.paperHullFirstCarrierCorrected (l := l) T b

theorem paperHullFirstCarrierCorrected_eq_least :
    paperHullFirstCarrierCorrected (l := l) T b =
      paperLeastLambdaOHull T b :=
  rfl

theorem paperHullFirstCarrierCorrected_subset_old :
    paperHullFirstCarrierCorrected (l := l) T b ⊆
      paperRootThetaHull (l := l) T b :=
  S810LeastHullPaperCarrierActual.paperHullFirstCarrierCorrected_subset_oldUnion
    (l := l) T b

end LeanFormal.IUT.XiFPaper.S797PaperHullFirstAuditActual

end

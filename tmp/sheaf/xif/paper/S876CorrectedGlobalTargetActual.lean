import tmp.sheaf.xif.paper.S860GlobalCor312AuditActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S876CorrectedGlobalTargetActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S860GlobalCor312AuditActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

abbrev PaperLeastHullData (b : Bad (nativePlaceSelection T)) : Type :=
  ArithmeticTuplePureFractionalScalingData (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily T b)

/-- Weighted sum of the paper-order qPilot log from the least hull. -/
noncomputable def paperQPilotWeightedLeast : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperQPilotLogLeast (l := l) T b

/-- Weighted sum of the least lambda*O hull log. -/
noncomputable def paperLeastHullWeightedLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      paperLeastLambdaOHullLog (l := l) T b Measure.addHaar

/-- Per-b S801/S799 equality gives the exact weighted equality. -/
theorem paperQPilotWeightedLeast_eq_leastHullWeighted
    (hdata : ∀ b : Bad (nativePlaceSelection T), PaperLeastHullData T b) :
    paperQPilotWeightedLeast T = paperLeastHullWeightedLog T := by
  unfold paperQPilotWeightedLeast paperLeastHullWeightedLog
  apply Finset.sum_congr rfl
  intro b _
  rw [paperQPilotLogLeast_eq_leastHullLog (l := l) T b Measure.addHaar (hdata b)]

/-- Corrected 2l global target. -/
def CorrectedGlobalTarget : Prop :=
  S860GlobalCor312AuditActual.weightedQPilot T ≤
    (2 * (l.value : Real)) * S860GlobalCor312AuditActual.thetaHullScalar T

/-- Conditional actual corrected target from the least-hull data and the two
weighted identifications. -/
theorem correctedGlobalTarget_of_weighted_identifications
    (hdata : ∀ b : Bad (nativePlaceSelection T), PaperLeastHullData T b)
    (hq : S860GlobalCor312AuditActual.weightedQPilot T =
      paperQPilotWeightedLeast T)
    (htheta : (2 * (l.value : Real)) *
      S860GlobalCor312AuditActual.thetaHullScalar T =
      paperLeastHullWeightedLog T) :
    CorrectedGlobalTarget T := by
  unfold CorrectedGlobalTarget
  rw [hq, htheta, paperQPilotWeightedLeast_eq_leastHullWeighted T hdata]

/-- Exact minimal gap if the two weighted identifications are not supplied. -/
def CorrectedGlobalTargetExactGap : Prop :=
  CorrectedGlobalTarget T

end LeanFormal.IUT.XiFPaper.S876CorrectedGlobalTargetActual
end
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual

/-! # S753: structural decomposition of the qPilot/Theta gap

(i) qPilotNormRegion ⊆ rootNormHull is actual;
(ii) normalized-log monotonicity is actual;
(iii) the identification of the qPilot log with the paper |log q| is the
remaining exact coefficient identification.
This file separates the three components; no OT/entropy data is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S753StructuralContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- Actual structural data for the qPilot/Theta comparison. -/
structure QPilotThetaStructuralData where
  qPilotImage : Set (qVFamTensorBlock T b)
  qPilotImage_eq : qPilotImage = qPilotNormRegion (l := l) T b
  thetaHull : Set (qVFamTensorBlock T b)
  thetaHull_eq : thetaHull = rootNormHull (l := l) T b
  containment : qPilotImage ⊆ thetaHull
  qPilotLog : Real
  qPilotLog_eq : qPilotLog = qPilotClassicalLog
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (rootNormCoefficient (l := l) T b) (rootNormScalingData (l := l) T b)
  thetaLog : Real
  thetaLog_eq : thetaLog = rootThetaHullLog
    (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (rootHalfCoefficient (l := l) T b)
  monotone : qPilotLog ≤ thetaLog

/-- Actual decomposition: containment and normalized-log monotonicity are
constructed without OT/entropy. -/
noncomputable def qPilotThetaStructuralData :
    QPilotThetaStructuralData (l := l) T b mu where
  qPilotImage := qPilotNormRegion (l := l) T b
  qPilotImage_eq := rfl
  thetaHull := rootNormHull (l := l) T b
  thetaHull_eq := rfl
  containment :=
    qPilotNormRegion_subset_rootNormHull (l := l) T b
  qPilotLog :=
    qPilotClassicalLog (qVFamTensorPlaces T b) qVFamTensorTuple mu
      (rootNormCoefficient (l := l) T b) (rootNormScalingData (l := l) T b)
  qPilotLog_eq := rfl
  thetaLog :=
    rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
      (rootHalfCoefficient (l := l) T b)
  thetaLog_eq := rfl
  monotone :=
    qPilotNormLog_le_rootNormHullLog (l := l) T b mu
      (qPilotNormRegion_measure_pos_lt_top (l := l) T b mu).1
      (rootNormHull_measure_lt_top (l := l) T b mu)

/-- Paper q[2u] scalar at b: -(order(q_v)/(2l)) log(p_v). -/
noncomputable def paperQLog : Real :=
  -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
    Real.log (qVFamTensorP T b : Real))

/-- (iii) The exact remaining identification: the normalized qPilot log equals
the paper q[2u] scalar -(order(q_v)/(2l)) log(p_v).  This is the exact
coefficient identification c_norm = order(q_v)/(2l), not a consequence of
(i)+(ii). -/
def PaperLogVolumeIdentification
    (D : QPilotThetaStructuralData (l := l) T b mu) : Prop :=
  D.qPilotLog = paperQLog (l := l) T b

/-- Actual structural inequality from (i)+(ii). -/
theorem structural_qPilotLog_le_thetaLog
    (D : QPilotThetaStructuralData (l := l) T b mu) :
    D.qPilotLog ≤ D.thetaLog :=
  D.monotone

/-- Conditional paper comparison from (i)+(ii)+(iii). -/
theorem paperQLog_le_thetaLog_of_identification
    (D : QPilotThetaStructuralData (l := l) T b mu)
    (h : PaperLogVolumeIdentification (l := l) T b mu D) :
    paperQLog (l := l) T b ≤ D.thetaLog := by
  rw [← h]
  exact D.monotone

/-- Exact missing data: an instance of the structural decomposition together
with the paper log identification. -/
structure PaperLogIdentificationData where
  structural : QPilotThetaStructuralData (l := l) T b mu
  paper_log_eq : PaperLogVolumeIdentification (l := l) T b mu structural

def PaperLogIdentificationDataRequired : Prop :=
  Nonempty (PaperLogIdentificationData (l := l) T b mu)

end LeanFormal.IUT.XiFPaper.S753StructuralContainmentActual
end

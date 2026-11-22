import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.IndActionsThetaLinkActual

/-!
# Ind3 output hull versus the actual q-pilot log-shell region

The actual multiradial output region used here is the root theta hull

  rootNormHull = closure (union_j F(j^2 c_root) O_hol)

on the actual qVFamily tensor block.  The actual q-pilot log-shell region is

  qPilotNormRegion = F(c_norm) O_hol.

RootNormalizedContainmentActual already proves

  qPilotNormRegion subset rootNormHull,

and RootHullMeasureActual supplies the actual positive/finite Haar facts with
no extra hypotheses.  RootHullContainmentInequalityActual then gives the actual
normalized-log comparison

  qPilotClassicalLog <= rootThetaHullLog.

This file packages exactly that actual containment/volume comparison.

The Ind3 stage-level upper-semi/log-Kummer action data lives on the
ActualInd3Stage carrier, not on the qVFamily tensor block.  An actual map from
the Ind3 stage image to rootNormHull is not supplied by the current tree; the
exact missing object is recorded as a Prop gap, not replaced by a value-layer
image or an enclosure.

No value-layer/enclosure shortcut, no fake inequality.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Ind3OutputHullQPilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.IndActionsThetaLinkActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b))
variable [Measure.IsAddHaarMeasure mu]

/-- The actual Ind3/multiradial output hull: the root theta hull with
coefficient c_root = c_norm/(2l). -/
noncomputable abbrev ind3OutputHull : Set (qVFamTensorBlock T b) :=
  rootNormHull (l := l) T b

/-- The actual q-pilot log-shell region. -/
noncomputable abbrev actualQPilotLogShellRegion : Set (qVFamTensorBlock T b) :=
  qPilotNormRegion (l := l) T b

/-- Actual containment: the q-pilot log-shell region is inside the actual
Ind3/multiradial output hull. -/
theorem actualQPilotLogShellRegion_subset_ind3OutputHull :
    actualQPilotLogShellRegion (l := l) T b ⊆
      ind3OutputHull (l := l) T b :=
  qPilotNormRegion_subset_rootNormHull (l := l) T b

/-- Actual positivity/finiteness of the q-pilot log-shell region. -/
theorem actualQPilotLogShellRegion_measure_pos_lt_top :
    0 < mu (actualQPilotLogShellRegion (l := l) T b) ∧
      mu (actualQPilotLogShellRegion (l := l) T b) < ⊤ :=
  qPilotNormRegion_measure_pos_lt_top (l := l) T b mu

/-- Actual finiteness of the Ind3/multiradial output hull. -/
theorem ind3OutputHull_measure_lt_top :
    mu (ind3OutputHull (l := l) T b) < ⊤ :=
  rootNormHull_measure_lt_top (l := l) T b mu

/-- Actual normalized-log comparison: the q-pilot log is at most the actual
Ind3/multiradial output hull log. -/
theorem actualQPilotLog_le_ind3OutputHullLog :
    qPilotClassicalLog
        (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (rootNormCoefficient (l := l) T b)
        (rootNormScalingData (l := l) T b) ≤
      rootThetaHullLog
        (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (rootHalfCoefficient (l := l) T b) :=
  qPilotNormLog_le_rootNormHullLog (l := l) T b mu
    (actualQPilotLogShellRegion_measure_pos_lt_top (l := l) T b mu).1
    (ind3OutputHull_measure_lt_top (l := l) T b mu)

/-- Actual containment/volume comparison data for the Ind3/multiradial output
hull and the q-pilot log-shell region. -/
structure Ind3OutputHullQPilotComparisonData where
  qPilotRegion : Set (qVFamTensorBlock T b)
  qPilotRegion_eq : qPilotRegion = actualQPilotLogShellRegion (l := l) T b
  outputHull : Set (qVFamTensorBlock T b)
  outputHull_eq : outputHull = ind3OutputHull (l := l) T b
  containment : qPilotRegion ⊆ outputHull
  qPilotLog : Real
  qPilotLog_eq : qPilotLog = qPilotClassicalLog
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (rootNormCoefficient (l := l) T b)
    (rootNormScalingData (l := l) T b)
  outputHullLog : Real
  outputHullLog_eq : outputHullLog = rootThetaHullLog
    (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (rootHalfCoefficient (l := l) T b)
  log_le : qPilotLog ≤ outputHullLog
  qPilotHaar_pos : 0 < mu qPilotRegion
  outputHullHaar_finite : mu outputHull < ⊤

/-- Actual comparison data. -/
noncomputable def ind3OutputHullQPilotComparisonData :
    Ind3OutputHullQPilotComparisonData (l := l) T b mu where
  qPilotRegion := actualQPilotLogShellRegion (l := l) T b
  qPilotRegion_eq := rfl
  outputHull := ind3OutputHull (l := l) T b
  outputHull_eq := rfl
  containment := actualQPilotLogShellRegion_subset_ind3OutputHull (l := l) T b
  qPilotLog := qPilotClassicalLog
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (rootNormCoefficient (l := l) T b)
    (rootNormScalingData (l := l) T b)
  qPilotLog_eq := rfl
  outputHullLog := rootThetaHullLog
    (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (rootHalfCoefficient (l := l) T b)
  outputHullLog_eq := rfl
  log_le := actualQPilotLog_le_ind3OutputHullLog (l := l) T b mu
  qPilotHaar_pos :=
    (actualQPilotLogShellRegion_measure_pos_lt_top (l := l) T b mu).1
  outputHullHaar_finite := ind3OutputHull_measure_lt_top (l := l) T b mu

/-- Exact missing object: an actual map from the Ind3 stage-level upper-semi
image (ActualInd3Stage) to the qVFamily tensor output hull.  The current tree
has the Ind3 action data and the root hull separately, but no actual
stage-to-region multiradial image. -/
structure Ind3StageToOutputHullGap : Type where
  actualStageImage : Prop
  stageImageToOutputHull : Prop
  stageImageLogCompatible : Prop
  notValueLayerOrEnclosure : Prop

/-- Exact missing Ind3 stage-to-output-hull image. -/
def Ind3StageToOutputHullGapRequired : Prop :=
  Nonempty Ind3StageToOutputHullGap

end LeanFormal.IUT.XiFPaper.Ind3OutputHullQPilotActual
end

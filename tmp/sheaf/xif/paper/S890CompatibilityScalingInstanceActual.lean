import tmp.sheaf.xif.paper.S889CompatibilityScalingGroupoid
import tmp.sheaf.xif.paper.S859PaperIntrinsicLogVolumeActual
import tmp.sheaf.xif.paper.S864PaperLambdaOLogVolumeActual

-- S890: actual instantiation of S889 scaling graph:
-- qClassical=-order log p, qRoot=-order/(2l) log p, thetaHull same.
-- Edges qRoot -> qClassical scale=2l, qRoot -> thetaHull scale=1.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S890CompatibilityScalingInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S889CompatibilityScalingGroupoid
open LeanFormal.IUT.XiFPaper.S859PaperIntrinsicLogVolumeActual
open LeanFormal.IUT.XiFPaper.S864PaperLambdaOLogVolumeActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual qPilot log: -order log p. -/
noncomputable def qClassicalLog : Real :=
  -paperIntrinsicLogVolume (l := l) T b (stackQSection (l := l) T b)

/-- Actual qRoot log: -order/(2l) log p. -/
noncomputable def qRootLog : Real :=
  -paperIntrinsicLogVolume (l := l) T b (stackRootSection (l := l) T b)

/-- Actual theta hull log: S864 paperLambdaOLogVolume cRoot. -/
noncomputable def thetaHullLog : Real :=
  paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b)

theorem qClassicalLog_eq :
    qClassicalLog (l := l) T b =
      -(((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real)) := by
  unfold qClassicalLog
  rw [paperIntrinsicLogVolume_q (l := l) T b]

theorem qRootLog_eq :
    qRootLog (l := l) T b =
      -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)) := by
  unfold qRootLog
  rw [paperIntrinsicLogVolume_root (l := l) T b]

theorem thetaHullLog_eq_qRootLog :
    thetaHullLog (l := l) T b = qRootLog (l := l) T b := by
  unfold thetaHullLog qRootLog
  rw [paperLambdaOLogVolume_cRoot_eq_neg_section (l := l) T b]

theorem qClassicalLog_eq_twoL_mul_qRootLog :
    qClassicalLog (l := l) T b =
      (2 * (l.value : Real)) * qRootLog (l := l) T b := by
  rw [qClassicalLog_eq (l := l) T b, qRootLog_eq (l := l) T b]
  have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  field_simp [hl]

inductive PilotObj
  | qClassical
  | qRoot
  | thetaHull

inductive PilotEdge : PilotObj → PilotObj → Type
  | qRootToQClassical : PilotEdge PilotObj.qRoot PilotObj.qClassical
  | qRootToThetaHull : PilotEdge PilotObj.qRoot PilotObj.thetaHull

noncomputable def pilotStep : {a b : PilotObj} → PilotEdge a b → Real
  | _, _, .qRootToQClassical => 2 * (l.value : Real)
  | _, _, .qRootToThetaHull => 1

noncomputable def pilotLogVolume : PilotObj → Real
  | .qClassical => qClassicalLog (l := l) T b
  | .qRoot => qRootLog (l := l) T b
  | .thetaHull => thetaHullLog (l := l) T b

theorem pilotEdge_law :
    ∀ {a c : PilotObj} (e : PilotEdge a c),
      pilotLogVolume (l := l) T b c =
        pilotStep (l := l) e * pilotLogVolume (l := l) T b a := by
  intro a c e
  cases e with
  | qRootToQClassical =>
      exact qClassicalLog_eq_twoL_mul_qRootLog (l := l) T b
  | qRootToThetaHull =>
      simp only [pilotStep, pilotLogVolume, one_mul]
      exact thetaHullLog_eq_qRootLog (l := l) T b

noncomputable def pilotScalingGraph : ScalingGraph where
  Obj := PilotObj
  Edge := PilotEdge
  step := pilotStep (l := l)
  logVolume := pilotLogVolume (l := l) T b
  edge_law := pilotEdge_law (l := l) T b

theorem qRoot_thetaHull_same_log :
    pilotLogVolume (l := l) T b PilotObj.qRoot =
      pilotLogVolume (l := l) T b PilotObj.thetaHull :=
  (thetaHullLog_eq_qRootLog (l := l) T b).symm

theorem paperQPilot_eq_qRoot_eq_hull :
    thetaHullLog (l := l) T b = qRootLog (l := l) T b ∧
      paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b) =
        thetaHullLog (l := l) T b := by
  constructor
  · exact thetaHullLog_eq_qRootLog (l := l) T b
  · rfl

#check pilotScalingGraph
#check pilotEdge_law
#check qRoot_thetaHull_same_log
#check paperQPilot_eq_qRoot_eq_hull

end LeanFormal.IUT.XiFPaper.S890CompatibilityScalingInstanceActual

end
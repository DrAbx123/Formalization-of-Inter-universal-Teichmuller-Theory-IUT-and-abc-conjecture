/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual

/-! A516/A517: q-pilot and Theta-pilot objects with their independent log
readouts, composed from green assets (Mzk1QPilotSHEDoubleImageActual, S201 root
norms, S3137 C3 hull readout). No q/(2l) definition and no comparison input. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotThetaObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The q-pilot local log object: the actual signed local q-log. -/
noncomputable def qPilotLocalLog : Real :=
  qPilotLogImage T b

theorem qPilotLocalLog_constructed :
    qPilotLocalLog T b = Real.log ‖(qVFamily T b).q‖ := rfl

/-- The Theta-pilot local log object: log norm of the actual root Theta value. -/
noncomputable def thetaPilotLocalLog (j : SignedLabel l.value) : Real :=
  Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖

theorem thetaPilotLocalLog_constructed (j : SignedLabel l.value) :
    thetaPilotLocalLog T b j =
      Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ := rfl

/-- The j^2 scaling of the Theta-pilot log: the local Theta log is the
gaussExponent power of the actual root log (Joshi ATS III / laichunwing 07). -/
theorem thetaPilotLocalLog_eq_gaussExponent (j : SignedLabel l.value) :
    thetaPilotLocalLog T b j =
      (gaussExponent j.1 : Real) * Real.log ‖rootNormedElement T b‖ := by
  unfold thetaPilotLocalLog
  rw [rootNormedThetaValueInL_norm, Real.log_zpow]

variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The q-pilot global readout on the actual C3 input. -/
noncomputable def qPilotGlobalLog
    (P : PaperQPilotObjectActual (l := l) (I := I)) : Real :=
  qPilotLogVolumeReading P

theorem qPilotGlobalLog_constructed
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qPilotGlobalLog C3 P = -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

/-- The Theta-pilot hull readout: actual Haar log-volume of the C3 hull. -/
noncomputable def thetaPilotHullLog : Real :=
  thetaPilotHullLogVolumeReal C3

theorem thetaPilotHullLog_constructed :
    thetaPilotHullLog C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

/-- The q/Theta pilot pair object on one bad place and one signed label. -/
structure QPilotThetaPilotObject (j : SignedLabel l.value) where
  qLocalLog : Real
  qLocalLog_eq : qLocalLog = qPilotLocalLog T b
  thetaLocalLog : Real
  thetaLocalLog_eq : thetaLocalLog = thetaPilotLocalLog T b j

noncomputable def qPilotThetaPilotObject (j : SignedLabel l.value) :
    QPilotThetaPilotObject T b j where
  qLocalLog := qPilotLocalLog T b
  qLocalLog_eq := rfl
  thetaLocalLog := thetaPilotLocalLog T b j
  thetaLocalLog_eq := rfl

theorem qPilotThetaPilotObject_constructed (j : SignedLabel l.value) :
    (qPilotThetaPilotObject T b j).qLocalLog = qPilotLocalLog T b ∧
      (qPilotThetaPilotObject T b j).thetaLocalLog =
        thetaPilotLocalLog T b j := by
  refine ⟨rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1QPilotThetaObjectActual
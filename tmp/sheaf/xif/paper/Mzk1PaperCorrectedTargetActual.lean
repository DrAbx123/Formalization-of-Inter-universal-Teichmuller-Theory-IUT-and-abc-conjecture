/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Paper312StatementActual
import tmp.sheaf.xif.paper.S3132PaperHullSetPropertiesActual
import Mathlib.Tactic

/-! # Canonical P0 target positioning (S3137 → Mzk1Paper312Statement → S3135)

The canonical paper component target is NOT the historical S800/S801 hull chain and NOT the
qVFam P4 hull.  It is:
* q side: `qPilotLogVolumeReading P = -|log ‖q‖|` (S3137 green);
* Theta side: `thetaPilotHullLogVolumeReal C3 = log(actualC3LogShellTensorHaar C3 (actual tensor region))`
  (S3137 green, raw Haar; hull = actual region);
* target: `Paper312Statement C3 P := qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3`
  (Mzk1Paper312StatementActual:49-50), equivalent to the still-PENDING
  `qThetaPilotLogVolumeComparison C3 P`.

S800 (`paperHullLog`, j=0-inclusive) and P4 (`paperFaithfulThetaHull`, nonzero qVFam labels)
are historical/side objects; see Mzk1PaperHullZeroLabelActual for the old-hull degeneration.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperCorrectedTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual
open LeanFormal.IUT.XiFPaper.S3132PaperHullSetPropertiesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open scoped ENNReal BigOperators

universe u

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

abbrev P0CanonicalTarget : Prop := Paper312Statement C3 P

theorem p0Target_iff_comparison :
    P0CanonicalTarget C3 P ↔ qThetaPilotLogVolumeComparison C3 P :=
  paper312Statement_iff_qThetaPilotLogVolumeComparison C3 P

theorem p0Target_iff_neg_abs_le :
    P0CanonicalTarget C3 P ↔
      -|Real.log (‖P.line.C3.q.q‖)| ≤ thetaPilotHullLogVolumeReal C3 :=
  paper312Statement_iff_neg_abs_le C3 P

theorem p0Target_iff_regionLogVolume :
    P0CanonicalTarget C3 P ↔
      -|Real.log (‖P.line.C3.q.q‖)| ≤
        Real.log ((actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3)).toReal :=
  paper312Statement_iff_regionLogVolume C3 P

def P0Gap : Prop := qThetaPilotLogVolumeComparison C3 P

theorem p0Target_iff_gap : P0CanonicalTarget C3 P ↔ P0Gap C3 P :=
  p0Target_iff_comparison C3 P

def rows : List (String × String × String) :=
  [ ("P0CanonicalTarget", "Paper312Statement = qPilotLogVolumeReading ≤ thetaPilotHullLogVolumeReal", "DEF"),
    ("p0Target_iff_comparison", "iff qThetaPilotLogVolumeComparison", "PROVED"),
    ("p0Target_iff_neg_abs_le", "-|log q| ≤ theta hull log", "PROVED"),
    ("p0Target_iff_regionLogVolume", "hull = actual tensor region", "PROVED"),
    ("P0Gap", "qThetaPilotLogVolumeComparison", "PENDING"),
    ("historical S800/S801 and qVFam P4", "not canonical P0", "SIDE OBJECTS") ]

theorem rows_length : rows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PaperCorrectedTargetActual

end
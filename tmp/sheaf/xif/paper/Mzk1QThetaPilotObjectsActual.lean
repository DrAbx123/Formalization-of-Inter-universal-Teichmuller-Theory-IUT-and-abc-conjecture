import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

/-!
# q-pilot / Theta-pilot object pair on the actual C3 input

Reference object layer over S3137: the actual q-pilot reading and the actual
Theta-pilot holomorphic hull are packaged as one pair.  The hull component is
the literal `thetaPilotHull C3`; the q component is the actual paper q-pilot.
No comparison is asserted. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1QThetaPilotObjectsActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- The two actual pilots on one C3 input: q-pilot object and Theta hull. -/
structure QThetaPilotPair (C3 : SourcePilotRegionData (l := l) (V := V) I) where
  /-- the actual paper q-pilot object. -/
  qPilot : PaperQPilotObjectActual (I := I)
  /-- the actual Theta-pilot holomorphic hull. -/
  thetaHull : Set (C3LogShellTensorBlock C3)

/-- The canonical pair from the actual S3137 constructions. -/
noncomputable def canonicalQThetaPilotPair
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (I := I)) : QThetaPilotPair C3 where
  qPilot := P
  thetaHull := thetaPilotHull C3

/-- `_constructed`: the hull component is the literal `thetaPilotHull C3`. -/
theorem canonical_thetaHull
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (I := I)) :
    (canonicalQThetaPilotPair C3 P).thetaHull = thetaPilotHull C3 :=
  rfl

/-- The q-hand reading of the pair is the reading of the q-pilot object. -/
theorem canonical_qPilot_reading
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (I := I)) :
    qPilotLogVolumeReading (canonicalQThetaPilotPair C3 P).qPilot =
      qPilotLogVolumeReading P :=
  rfl

/-- The q-reading equals `-|log q|` for the actual source completion q. -/
theorem canonical_qPilot_reading_eq_neg_abs_q
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (I := I)) :
    qPilotLogVolumeReading (canonicalQThetaPilotPair C3 P).qPilot =
      -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

/-- The Theta-pilot hull log-volume is finite. -/
theorem canonical_thetaHull_logVolume_ne_top
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (I := I)) :
    thetaPilotHullLogVolume C3 ≠ ⊤ :=
  thetaPilotHullLogVolume_ne_top C3

/-- The real Theta-pilot hull log-volume is the region log-volume. -/
theorem canonical_thetaHull_logVolumeReal_eq_region
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (P : PaperQPilotObjectActual (I := I)) :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_regionLogVolume C3

#check canonicalQThetaPilotPair
#check canonical_qPilot_reading_eq_neg_abs_q

end LeanFormal.IUT.XiFPaper.Mzk1QThetaPilotObjectsActual
end

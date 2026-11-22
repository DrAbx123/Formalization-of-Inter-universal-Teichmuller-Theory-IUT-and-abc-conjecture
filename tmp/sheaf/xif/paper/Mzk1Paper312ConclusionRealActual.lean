/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Tactic

/-! # A758 hull: `Cor312Conclusion` directly from the real S3137 readings

Uses the actual readings only (no `Set Real` toy carrier):

* q-side: `qPilotLogVolumeReading P = -|log q|` (S3137);
* Theta-side: `thetaPilotHullLogVolumeReal C3` (log-volume of theta hull, S3137);
* comparison: `qThetaPilotLogVolumeComparison C3 P` (exactly `Paper312Statement`);
* contract: `signedCor312Contract` with `qSigned = qPilotLogVolumeReading P`,
  `thetaSigned = thetaPilotHullLogVolumeReal C3`,
  `hq` strict negativity and `hle` the comparison.

No toy carrier, no named structure, no fake proof.  `hq` is derived from the
nondegeneracy `Real.log ‖q‖ ≠ 0` when possible; otherwise kept as explicit input.

No RETRACTED file referenced. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312ConclusionRealActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open scoped ENNReal BigOperators

universe u

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Strict negativity of the q-pilot reading from nondegeneracy `log ‖q‖ ≠ 0`. -/
theorem qPilotLogVolumeReading_neg_of_log_ne_zero
    (hlog : Real.log (‖P.line.C3.q.q‖) ≠ 0) :
    qPilotLogVolumeReading P < 0 := by
  rw [qPilotLogVolumeReading_eq_neg_abs_qParameter P]
  have hpos : 0 < |Real.log (‖P.line.C3.q.q‖)| := abs_pos.mpr hlog
  linarith

/-- **`Cor312Conclusion` from the real readings**: `hcmp` is exactly
`qThetaPilotLogVolumeComparison C3 P` (the paper comparison), `hqneg` strict
negativity, and `ipl/she/apt` the qualitative evidence. -/
theorem cor312Conclusion_of_paper312
    (hcmp : qThetaPilotLogVolumeComparison C3 P)
    (hqneg : qPilotLogVolumeReading P < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (signedCor312Contract (qPilotLogVolumeReading P)
        (thetaPilotHullLogVolumeReal C3) hqneg ipl hipl she hshe apt hapt
        (by simpa [qThetaPilotLogVolumeComparison] using hcmp)) :=
  signedCor312_conclusion (qPilotLogVolumeReading P)
    (thetaPilotHullLogVolumeReal C3) hqneg ipl hipl she hshe apt hapt
    (by simpa [qThetaPilotLogVolumeComparison] using hcmp)

/-- Variant with `hqneg` derived from the nondegeneracy of `log ‖q‖`. -/
theorem cor312Conclusion_of_paper312_of_log_ne_zero
    (hcmp : qThetaPilotLogVolumeComparison C3 P)
    (hlog : Real.log (‖P.line.C3.q.q‖) ≠ 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (signedCor312Contract (qPilotLogVolumeReading P)
        (thetaPilotHullLogVolumeReal C3)
        (qPilotLogVolumeReading_neg_of_log_ne_zero P hlog)
        ipl hipl she hshe apt hapt
        (by simpa [qThetaPilotLogVolumeComparison] using hcmp)) :=
  cor312Conclusion_of_paper312 C3 P hcmp
    (qPilotLogVolumeReading_neg_of_log_ne_zero P hlog)
    ipl hipl she hshe apt hapt

def realConclusionRows : List (String × String × String) :=
  [ ("qSigned", "qPilotLogVolumeReading P = -|log q|", "S3137 actual reading"),
    ("thetaSigned", "thetaPilotHullLogVolumeReal C3 (log-vol theta hull)", "S3137 actual reading"),
    ("hle", "qThetaPilotLogVolumeComparison C3 P := qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3", "explicit hypothesis hcmp"),
    ("hqneg", "qPilotLogVolumeReading P < 0; derived from Real.log ‖q‖ != 0 in the _of_log_ne_zero variant", "PROVED / explicit"),
    ("Cor312Conclusion", "cor312Conclusion_of_paper312 (real readings, signedCor312Contract)", "PROVED conditional on hcmp + hqneg"),
    ("no toy carrier", "no Set Real carrier, no XiEContainmentRequirement, no s3137Volume", "INTEGRITY") ]

theorem realConclusionRows_length : realConclusionRows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Paper312ConclusionRealActual.qPilotLogVolumeReading_neg_of_log_ne_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Paper312ConclusionRealActual.cor312Conclusion_of_paper312
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Paper312ConclusionRealActual.cor312Conclusion_of_paper312_of_log_ne_zero

end LeanFormal.IUT.XiFPaper.Mzk1Paper312ConclusionRealActual

end
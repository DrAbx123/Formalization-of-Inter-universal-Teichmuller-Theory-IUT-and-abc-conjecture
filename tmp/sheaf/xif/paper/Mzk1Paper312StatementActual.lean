import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Tactic

/-!
# A757 Paper 3.12 statement on the actual S3137 readings (shehdd owner)

The true paper 3.12 statement is the comparison of the actual q-pilot reading
`qPilotLogVolumeReading P = -|log q|` with the actual Theta-pilot hull log-volume
`thetaPilotHullLogVolumeReal C3` (S3137):

`Paper312Statement C3 P := qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3`,

which is exactly S3137's named candidate `qThetaPilotLogVolumeComparison`
(`Q_C <= H_C`, Step (xi-f)); it is the precise remaining gap and is NOT proved.

No toy carrier: the conditional contract below is built directly on the actual
S3137 readings (no `Set Real := {0}` surrogate, no if/else volume).
The rejected `Mzk1ThetaValue312Actual` is history only and not referenced.

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- **The true paper 3.12 statement** on the actual S3137 readings: the q-pilot
log-volume reading is at most the Theta-pilot hull log-volume reading. -/
def Paper312Statement : Prop :=
  qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3

theorem paper312Statement_iff_qThetaPilotLogVolumeComparison :
    Paper312Statement C3 P ↔ qThetaPilotLogVolumeComparison C3 P :=
  Iff.rfl

/-- Expanded paper form: `-|log q| <= theta-hull log-volume`. -/
theorem paper312Statement_iff_neg_abs_le :
    Paper312Statement C3 P ↔
      -|Real.log (‖P.line.C3.q.q‖)| ≤
        thetaPilotHullLogVolumeReal C3 := by
  unfold Paper312Statement
  rw [qPilotLogVolumeReading_eq_neg_abs_qParameter]

/-- Expanded on the actual tensor log-shell region (hull = region, S3137). -/
theorem paper312Statement_iff_regionLogVolume :
    Paper312Statement C3 P ↔
      -|Real.log (‖P.line.C3.q.q‖)| ≤
        Real.log ((actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3)).toReal :=
  by
  rw [paper312Statement_iff_neg_abs_le,
    thetaPilotHullLogVolumeReal_eq_regionLogVolume]

/-- The q-pilot reading is strictly negative on the actual source. -/
theorem paper312_qReading_neg : qPilotLogVolumeReading P < 0 :=
  P.signedQPilotLogVolume_neg

/-- **Conditional StepXI conclusion on the actual readings**: `Paper312Statement`
gives `Cor312Conclusion` of the signed contract whose q/Theta values are literally
the S3137 readings (no toy volume). -/
theorem cor312_of_paper312Statement (h : Paper312Statement C3 P)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (signedCor312Contract (qPilotLogVolumeReading P)
        (thetaPilotHullLogVolumeReal C3) (paper312_qReading_neg P)
        ipl hipl she hshe apt hapt h) :=
  signedCor312_conclusion (qPilotLogVolumeReading P)
    (thetaPilotHullLogVolumeReal C3) (paper312_qReading_neg P)
    ipl hipl she hshe apt hapt h

/-- The conditional contract's comparison is literally `Paper312Statement`. -/
theorem cor312_of_paper312Statement_comparison (h : Paper312Statement C3 P) :
    (signedCor312Contract (qPilotLogVolumeReading P)
        (thetaPilotHullLogVolumeReal C3) (paper312_qReading_neg P)
        True trivial True trivial True trivial h).qSigned ≤
      (signedCor312Contract (qPilotLogVolumeReading P)
        (thetaPilotHullLogVolumeReal C3) (paper312_qReading_neg P)
        True trivial True trivial True trivial h).thetaSigned :=
  h

structure StatementRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def statementRows : List StatementRow :=
  [ ⟨"paper statement", "Paper312Statement C3 P := qPilotLogVolumeReading P <= thetaPilotHullLogVolumeReal C3", "REAL_PROP"⟩
  , ⟨"S3137 equivalence", "iff qThetaPilotLogVolumeComparison C3 P", "PROVED"⟩
  , ⟨"expanded q form", "-|log q| <= theta-hull log-volume", "PROVED"⟩
  , ⟨"expanded region form", "theta-hull log-volume = log Haar(actual tensor region)", "PROVED"⟩
  , ⟨"conditional 3.12", "Paper312Statement -> Cor312Conclusion via signed contract on the readings", "GREEN_CONDITIONAL"⟩
  , ⟨"remaining gap", "prove Paper312Statement C3 P for all actual C3/P (equivalently qThetaPilotLogVolumeComparison)", "SINGLE_GAP"⟩
  , ⟨"toy carrier", "Mzk1ThetaValue312Actual REJECTED history; not referenced", "REJECTED_HISTORY"⟩
  , ⟨"scope", "no retracted use; no if/else volume", "INTEGRITY"⟩
  ]

theorem statementRows_length : statementRows.length = 8 := rfl

theorem statementRows_has_single_gap :
    statementRows.any (fun r => r.status = "SINGLE_GAP") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual.paper312Statement_iff_qThetaPilotLogVolumeComparison
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual.paper312Statement_iff_regionLogVolume
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual.cor312_of_paper312Statement

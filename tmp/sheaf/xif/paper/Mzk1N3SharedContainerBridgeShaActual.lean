import tmp.sheaf.xif.paper.Mzk1N3SharedContainerRealActual
import tmp.sheaf.xif.paper.Mzk1Paper312ConclusionRealActual
import tmp.sheaf.xif.paper.Mzk1Paper312StatementActual
import Mathlib.Tactic

/-!
# A760 N3 shared-container bridge (shehdd): qpilot real container ↔ paper 3.12 statement

qpilot's `Mzk1N3SharedContainerRealActual` constructs the real S3137 carrier
`C3LogShellTensorBlock C3` with the actual Haar volume reading and both pilot
readings, and records the paper gap `paperGap D` (NOT proved).  This bridge proves:

* `paperGap D` is exactly shehdd's `Paper312Statement C3 P` (and S3137's
  `qThetaPilotLogVolumeComparison`);
* on the constructed container `paperSharedContainerReal C3 P`, `paperGap` is the
  actual q-pilot/Theta-hull comparison;
* `paperGap` + q-negativity gives `Cor312Conclusion` through qpilot's real-readings
  signed contract (no toy carrier, no XiEContainmentRequirement surrogate).

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerBridgeShaActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerRealActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ConclusionRealActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
variable (D : SharedContainerReal (l := l) (I := I) C3 P)

/-- qpilot's real-container paper gap is exactly the actual S3137 comparison. -/
theorem paperGap_iff_qThetaComparison :
    paperGap D ↔ qThetaPilotLogVolumeComparison C3 P := by
  unfold paperGap qThetaPilotLogVolumeComparison
  rw [D.qPilotVolumeReading_eq, D.thetaPilotVolumeReading_eq]

/-- qpilot's paper gap is exactly shehdd's `Paper312Statement`. -/
theorem paperGap_iff_paper312Statement :
    paperGap D ↔
      LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual.Paper312Statement C3 P := by
  rw [paperGap_iff_qThetaComparison]
  rfl

/-- The constructed real container's paper gap is the actual S3137 comparison. -/
theorem paperSharedContainerReal_paperGap_iff :
    paperGap (paperSharedContainerReal (l := l) (I := I) C3 P) ↔
      qThetaPilotLogVolumeComparison C3 P := by
  rw [paperGap_iff_qThetaComparison]

/-- **Real-container conditional 3.12**: the paper gap on the shared container plus
q-negativity yields `Cor312Conclusion` via qpilot's real-readings contract. -/
theorem cor312_of_sharedPaperGap (hcmp : paperGap D)
    (hqneg : qPilotLogVolumeReading P < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (signedCor312Contract (qPilotLogVolumeReading P)
        (thetaPilotHullLogVolumeReal C3) hqneg ipl hipl she hshe apt hapt
        (by simpa [qThetaPilotLogVolumeComparison] using
          (paperGap_iff_qThetaComparison C3 P D).mp hcmp)) :=
  cor312Conclusion_of_paper312 C3 P
    ((paperGap_iff_qThetaComparison C3 P D).mp hcmp) hqneg
    ipl hipl she hshe apt hapt

structure BridgeRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def bridgeRows : List BridgeRow :=
  [ ⟨"container", "qpilot Mzk1N3SharedContainerRealActual (real C3 carrier + Haar reading + pilot readings)", "GREEN"⟩
  , ⟨"gap", "paperGap D recorded, not proved (paper Q_C <= H_C)", "SINGLE_GAP"⟩
  , ⟨"bridge 1", "paperGap D <-> qThetaPilotLogVolumeComparison C3 P", "PROVED"⟩
  , ⟨"bridge 2", "paperGap D <-> Paper312Statement C3 P (shehdd)", "PROVED"⟩
  , ⟨"bridge 3", "paperGap D + q-neg -> Cor312Conclusion (real readings contract)", "PROVED"⟩
  , ⟨"scope", "no toy carrier; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem bridgeRows_length : bridgeRows.length = 6 := rfl

theorem bridgeRows_has_single_gap :
    bridgeRows.any (fun r => r.status = "SINGLE_GAP") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerBridgeShaActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerBridgeShaActual.paperGap_iff_qThetaComparison
#print axioms LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerBridgeShaActual.paperGap_iff_paper312Statement
#print axioms LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerBridgeShaActual.cor312_of_sharedPaperGap

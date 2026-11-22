import tmp.sheaf.xif.paper.Mzk1Stage4ABCGapEstimatesActual
import tmp.sheaf.xif.paper.Mzk1Stage4HeightEstimateActual
import tmp.sheaf.xif.paper.Mzk1Stage4GapStructuralConsumerActual
import tmp.sheaf.xif.paper.Mzk1Stage4A618AuditProofActual
import tmp.sheaf.xif.paper.Mzk1Stage4GapComponentSeparationActual
import tmp.sheaf.xif.paper.Mzk1Stage4AuditSummaryActual

/-! # Mzk1Stage4FinalConsumerWrapupActual (stage4 lane; consumer wrap-up)

A645 module: final stage4 consumer wrap-up — one thin consumer per green stage4 chain
(gap structural, A618 audit proof, gap components, final-chain audit), with axiom prints.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalConsumerWrapupActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4ABCGapEstimatesActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightEstimateActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapStructuralConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4GapComponentSeparationActual

/-- Wrap-up consumer 1: the gap structural height bound. -/
theorem wrapup_gap_height :
    Mzk1Stage4HeightEstimateActual.height11 ≤ (1 + 1 / 10 : Real) * Real.log 11 + (11 + 0) :=
  gapStructuralConsumer_height

/-- Wrap-up consumer 2: Gap 1 iff form (component separation). -/
theorem wrapup_gap1_iff (height regionVol : Real) :
    Gap1 height regionVol ↔ height ≤ regionVol :=
  gap1_iff height regionVol

/-- Wrap-up consumer 3: Gap 2 iff form (component separation). -/
theorem wrapup_gap2_iff (regionVol weight hull D eps : Real) :
    Gap2 regionVol weight hull D eps ↔ regionVol ≤ (1 + eps) * weight + hull + D :=
  gap2_iff regionVol weight hull D eps

/-- Wrap-up consumer 4: the audited final-chain registry length. -/
theorem wrapup_audited_length :
    Mzk1Stage4AuditSummaryActual.auditedTheorems.length = 7 :=
  Mzk1Stage4AuditSummaryActual.auditedTheorems_length

#print axioms wrapup_gap_height
#print axioms wrapup_gap1_iff
#print axioms wrapup_gap2_iff

#check wrapup_gap_height
#check wrapup_gap1_iff
#check wrapup_gap2_iff
#check wrapup_audited_length

end LeanFormal.IUT.XiFPaper.Mzk1Stage4FinalConsumerWrapupActual
end

import tmp.sheaf.xif.paper.Mzk1CorrectedRegionLogLawProvedActual
import tmp.sheaf.xif.paper.Mzk1CorrectedGap1UnconditionalActual
import Mathlib.Tactic

/-! # shehdd carrier log law gate (Sha, read-only, no new objects) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleLogShaActual

structure CarrierLogRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def carrierLogRows : List CarrierLogRow :=
  [ ⟨"unit-region corrected log law", "Mzk1CorrectedRegionLogLawProvedActual.corrected_unitRegion_logLaw", "GREEN"⟩
  , ⟨"full corrected-region log law", "Mzk1CorrectedGap1UnconditionalActual.correctedRegion_logLaw", "GREEN"⟩
  , ⟨"scope", "gate only; no gap claimed", "INTEGRITY"⟩
  ]

theorem carrierLogRows_length : carrierLogRows.length = 3 := rfl

theorem carrierLogRows_statuses_ok :
    carrierLogRows.all (fun r => r.status ∈ ["GREEN", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1CarrierBadInvScaleLogShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawProvedActual.corrected_unitRegion_logLaw
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalActual.correctedRegion_logLaw

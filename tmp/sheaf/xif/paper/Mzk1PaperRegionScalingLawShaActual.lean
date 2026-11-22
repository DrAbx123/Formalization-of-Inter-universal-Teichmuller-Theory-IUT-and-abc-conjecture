import tmp.sheaf.xif.paper.Mzk1Gap1ScalingLawTargetActual
import tmp.sheaf.xif.paper.Mzk1Stage4Gap1ScalingLawConsumerActual
import tmp.sheaf.xif.paper.Mzk1Gap1FullRatioScalingElementAuditShaActual

/-!
# shehdd A664 PaperRegionScalingLaw proof-surface gate (Sha, read-only)

Consumes the green `PaperRegionScalingLaw` proof surface and records the status of
the A664 triple:
* `PaperRegionScalingLaw` definition and its Gap-1 reductions are GREEN
  (`gap1_of_scalingLaw_and_arith`, `gap1_arithmetic_condition_iff`, `gap1_of_fullRatio`);
* the stage-4 full-ratio consumer `stage4_gap1_fullRatio` is GREEN;
* shehdd full-ratio theorem `gap1_full_ratio_form` is GREEN (independent corroboration);
* `CarrierScalingLogLaw` (normalized carrier log form) is still PENDING_MAINLINE;
  the shehdd conditional log form is `Mzk1CarrierBadInvScaleLogShaActual`
  (PENDING_FRESH).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperRegionScalingLawShaActual

structure ScalingLawRow where
  item : String
  source : String
  status : String
  deriving Repr, DecidableEq

def scalingLawRows : List ScalingLawRow :=
  [ ⟨"PaperRegionScalingLaw definition", "Mzk1Gap1ScalingLawTargetActual.PaperRegionScalingLaw", "GREEN"⟩
  , ⟨"scaling law + arithmetic => Gap1", "gap1_of_scalingLaw_and_arith", "GREEN"⟩
  , ⟨"arithmetic condition equivalence", "gap1_arithmetic_condition_iff", "GREEN"⟩
  , ⟨"full-ratio reduction", "gap1_of_fullRatio", "GREEN"⟩
  , ⟨"stage-4 full-ratio consumer", "Mzk1Stage4Gap1ScalingLawConsumerActual.stage4_gap1_fullRatio", "GREEN"⟩
  , ⟨"shehdd full-ratio", "Mzk1Gap1FullRatioScalingElementAuditShaActual.gap1_full_ratio_form", "GREEN"⟩
  , ⟨"CarrierScalingLogLaw (normalized)", "mainline file not created yet", "PENDING_MAINLINE"⟩
  , ⟨"shehdd carrier log form", "Mzk1CarrierBadInvScaleLogShaActual.log_badInvScale_productHaar_pi", "PENDING_FRESH"⟩
  , ⟨"badPart arithmetic", "Mzk1CarrierBadInvScaleBadPartShaActual", "GREEN"⟩
  , ⟨"scope", "gate/status only; named gaps unchanged", "INTEGRITY"⟩
  ]

def allowedStatuses : List String :=
  ["GREEN", "PENDING_MAINLINE", "PENDING_FRESH", "INTEGRITY"]

theorem scalingLawRows_length : scalingLawRows.length = 10 := rfl

theorem scalingLawRows_statuses_ok :
    scalingLawRows.all (fun r => r.status ∈ allowedStatuses) = true := by
  decide

theorem scalingLaw_has_paper_law :
    scalingLawRows.any (fun r => r.item = "PaperRegionScalingLaw definition") = true := by
  decide

theorem scalingLaw_has_carrier_pending :
    scalingLawRows.any (fun r => r.status = "PENDING_MAINLINE") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1PaperRegionScalingLawShaActual

/-! ### Axiom gates (read-only) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual.gap1_of_scalingLaw_and_arith
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual.gap1_of_fullRatio
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap1ScalingLawConsumerActual.stage4_gap1_fullRatio

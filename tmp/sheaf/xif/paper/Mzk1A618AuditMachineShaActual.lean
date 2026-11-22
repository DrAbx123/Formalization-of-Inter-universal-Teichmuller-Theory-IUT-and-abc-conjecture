import Mathlib.Tactic

/-!
# shehdd A618/A620 audit mechanization (machine-readable rows + checks, dependency-free)

Machine-checkable audit table for the S1902 bridge / two-estimates lane.
This file is dependency-free (Mathlib.Tactic only) so it is green independently
of pending bridge oleans.  Rows record name/source/status; checks are by `decide`.

Updated A620: canonical mainline `Mzk1S1902BridgeInterfaceActual` is GREEN
(EXIT=0, gate trio) and hull's `Mzk1S1902IQHullInterfaceActual` is GREEN_OLE_TRUE.
A622 note: canonical triple-dependent scaling file
`Mzk1PaperComparisonRegionScalingActual` is mainline-exclusive; its design row is
recorded as NAMED (paper input), not claimed here.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1A618AuditMachineShaActual

structure AuditRow where
  name : String
  source : String
  status : String
  deriving Repr, DecidableEq

def allowedStatuses : List String :=
  ["GREEN", "GREEN_OLE_TRUE", "PENDING", "NAMED", "SUPPLEMENTARY",
   "SUPPLEMENTARY_MODEL_ONLY", "NAMED_AUDIT", "RED"]

def auditRows : List AuditRow :=
  [ ⟨"canonical hull S1902 IQ instance", "hull: Mzk1S1902IQHullInterfaceActual", "GREEN_OLE_TRUE"⟩
  , ⟨"canonical mainline S1902 bridge", "mainline: Mzk1S1902BridgeInterfaceActual", "GREEN"⟩
  , ⟨"Gap1 height estimate", "height_le_normalizedRegionVolume (NAMED)", "NAMED"⟩
  , ⟨"Gap2 volume estimate", "regionVolume <= (1+eps)weight + hull + D (NAMED)", "NAMED"⟩
  , ⟨"triple-dependent scaling design", "A622 Mzk1PaperComparisonRegionScalingActual (mainline)", "NAMED"⟩
  , ⟨"shehdd S1902 concrete bridge (Sha)", "Mzk1S1902ConcreteBridgeShaActual", "PENDING"⟩
  , ⟨"shehdd canonical-hullData bridge (Sha)", "Mzk1S1902CanonicalBridgeShaActual", "PENDING"⟩
  , ⟨"real-model ABCTwoEstimates (Sha)", "Mzk1ABCTwoEstimatesRealModelShaActual", "PENDING"⟩
  , ⟨"weight-model height equivalence", "Mzk1ABCTwoEstimatesHeightWeightShaActual", "SUPPLEMENTARY_MODEL_ONLY"⟩
  , ⟨"real height interface (region log-volume)", "Mzk1ABCTwoEstimatesAuditCorrectionShaActual", "SUPPLEMENTARY"⟩
  , ⟨"3+125=128 height>weight counterexample", "audit note (3+125=128, rad=30)", "NAMED_AUDIT"⟩
  , ⟨"hqneg clean gate", "Mzk1HqnegCleanGateShaActual", "GREEN_OLE_TRUE"⟩
  , ⟨"hqneg discharged acceptance", "Mzk1Cor312HqnegDischargedActual (mainline)", "GREEN"⟩
  ]

theorem auditRows_length : auditRows.length = 13 := rfl

theorem auditRows_allowed :
    auditRows.all (fun r => r.status ∈ allowedStatuses) = true := by
  decide

theorem audit_has_gap1 :
    auditRows.any (fun r => r.name = "Gap1 height estimate") = true := by
  decide

theorem audit_has_gap2 :
    auditRows.any (fun r => r.name = "Gap2 volume estimate") = true := by
  decide

theorem audit_has_triple_scaling :
    auditRows.any (fun r => r.name = "triple-dependent scaling design") = true := by
  decide

theorem audit_has_canonical_bridge_green :
    auditRows.any (fun r => r.name = "canonical mainline S1902 bridge" ∧ r.status = "GREEN") = true := by
  decide

theorem audit_has_counterexample :
    auditRows.any (fun r => r.name = "3+125=128 height>weight counterexample") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1A618AuditMachineShaActual

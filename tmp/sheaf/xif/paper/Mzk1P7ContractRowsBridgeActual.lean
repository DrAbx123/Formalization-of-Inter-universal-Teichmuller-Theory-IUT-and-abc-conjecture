/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P7ContractMapActual
import tmp.sheaf.xif.paper.Mzk1P7ContractMarginConsumerActual
import Mathlib.Tactic

/-! # P7/#8 bridge: margin7Rows aligns with missing7ToGap (items, codes, order) -/

/-
| field | value |
|---|---|
| Status | PROVED (rfl): `margin7Rows` and `missing7ToGap` have identical item names, gap codes and order |
| GAP | GAP-P7-CONTRACT remains CONDITIONAL; rows 2–7 unchanged, row 1 carries the margin/dictionary condition |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P7ContractRowsBridgeActual

open LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ContractMarginConsumerActual

/-- Row item names of `margin7Rows` are exactly those of `missing7ToGap`. -/
theorem margin7Rows_items_eq_missing7ToGap :
    margin7Rows.map (fun r => r.1) = missing7ToGap.map (fun r => r.1) := rfl

/-- Gap codes of `margin7Rows` are exactly those of `missing7ToGap`. -/
theorem margin7Rows_codes_eq_missing7ToGap :
    margin7Rows.map (fun r => r.2.1) = missing7ToGap.map (fun r => r.2.1) := rfl

/-- Length/order alignment: both lists have 7 rows. -/
theorem margin7Rows_length_eq_missing7ToGap :
    margin7Rows.length = missing7ToGap.length := rfl


/-- Evidence-upgraded status of the 7 missing reconciliation items (current tree). -/
def missing7ToGapEvidence : List (String × String × String) :=
  [ ("general qThetaPilotLogVolumeComparison", "GAP-P7-GENERAL-CMP", "GAP (comparison still open)"),
    ("paper carrier IQ realization", "GAP-P7-IQ-LITERAL", "GAP (carrier interface only)"),
    ("(Ob3-3) source identification", "GAP-P7-OB33-SRC", "PROVED (Mzk1Ob33DetLineBridgeActual + B5Index generator; no assumptions)"),
    ("multiradial (xi-e)/(xi-f) production", "GAP-P7-MULTIRADIAL", "GAP (production not formalized)"),
    ("theta raw Haar vs paper normalized V", "GAP-P7-THETA-V / D / DEG", "PARTIAL (B5-1 unconditional; B5-3 arch proved; generator closed)"),
    ("StepXIContract fields/linkage", "GAP-P7-CONTRACT", "GAP (ContractFieldsLinked = false)"),
    ("exact hull volume upper bound", "GAP-P7-HULL-UB", "GAP (upper-bound interface only)") ]

theorem missing7ToGapEvidence_length : missing7ToGapEvidence.length = 7 := rfl

/-- The evidence table covers exactly the same 7 item names as missing7ToGap. -/
theorem missing7ToGapEvidence_items_eq :
    missing7ToGapEvidence.map (fun r => r.1) = missing7ToGap.map (fun r => r.1) := by
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7ContractRowsBridgeActual
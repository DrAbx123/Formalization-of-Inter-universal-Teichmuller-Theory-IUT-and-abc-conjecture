/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P7ContractMapActual
import tmp.sheaf.xif.paper.Mzk1DetLineConstructionActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineBridgeActual
import tmp.sheaf.xif.paper.Mzk1B5FractionalExpansionUncondActual
import tmp.sheaf.xif.paper.Mzk1B5RelativeDetLogExpansionActual
import Mathlib.Tactic

/-! # P7 #8: evidence rows for the 7 missing items -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapEvidenceRowsActual

open LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapActual

/-- Upgraded status of the 7 missing reconciliation items, with actual evidence. -/
def missing7ToGapEvidence : List (String × String × String × String) :=
  [ ("general qThetaPilotLogVolumeComparison", "GAP-P7-GENERAL-CMP", "GAP", "comparison still open"),
    ("paper carrier IQ realization", "GAP-P7-IQ-LITERAL", "GAP", "carrier interface only"),
    ("(Ob3-3) source identification", "GAP-P7-OB33-SRC", "PROVED", "Mzk1Ob33DetLineBridgeActual (actual source + relative det log)"),
    ("multiradial (xi-e)/(xi-f) production", "GAP-P7-MULTIRADIAL", "GAP", "production not formalized"),
    ("theta raw Haar vs paper normalized V", "GAP-P7-THETA-V / D / DEG", "PARTIAL", "B5 (1) unconditional: Mzk1B5FractionalExpansionUncondActual; B5 (3) arch: Mzk1B5RelativeDetLogExpansionActual"),
    ("StepXIContract fields/linkage", "GAP-P7-CONTRACT", "GAP", "ContractFieldsLinked = false (p7_contract_fields_not_linked)"),
    ("exact hull volume upper bound", "GAP-P7-HULL-UB", "GAP", "hull upper bound interface only") ]

theorem missing7ToGapEvidence_length : missing7ToGapEvidence.length = 7 := rfl

/-- Rows whose status is upgraded from GAP to PROVED by actual evidence. -/
def evidenceUpgradeRows : List (String × String × String) :=
  [ ("B5 relative determinant log (1)", "Mzk1B5FractionalExpansionUncondActual", "PROVED (unconditional)"),
    ("B5 arch summary (3)", "Mzk1B5RelativeDetLogExpansionActual", "PROVED (conditional on bridges)"),
    ("Ob33 actual source -> relative det log", "Mzk1Ob33DetLineBridgeActual", "PROVED"),
    ("B4/B5 global relative det log", "Mzk1DetLineConstructionActual", "PROVED"),
    ("remaining true GAPs", "R21Bridge / (Ob3-3) semantic identification / comparison / hull UB", "GAP") ]

theorem evidenceUpgradeRows_length : evidenceUpgradeRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapEvidenceRowsActual

end
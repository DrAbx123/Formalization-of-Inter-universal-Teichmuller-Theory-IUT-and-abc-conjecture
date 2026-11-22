/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P7ContractMapEvidenceRowsActual
import Mathlib.Tactic

/-! # P7 #8: final evidence rows -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapEvidenceFinalActual

open LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapEvidenceRowsActual

def missing7ToGapEvidenceFinal : List (String × String × String) :=
  [ ("general comparison", "GAP-P7-GENERAL-CMP", "GAP"),
    ("paper carrier IQ", "GAP-P7-IQ-LITERAL", "GAP"),
    ("Ob3-3 source identification", "GAP-P7-OB33-SRC", "PROVED (Mzk1Ob33DetLineBridgeActual)"),
    ("multiradial", "GAP-P7-MULTIRADIAL", "GAP"),
    ("theta raw Haar vs paper V", "GAP-P7-THETA-V/D/DEG", "PARTIAL (B5-1 unconditional, B5-3 arch proved)"),
    ("StepXI contract/linkage", "GAP-P7-CONTRACT", "GAP (ContractFieldsLinked=false)"),
    ("hull upper bound", "GAP-P7-HULL-UB", "GAP") ]

theorem missing7ToGapEvidenceFinal_length : missing7ToGapEvidenceFinal.length = 7 := rfl

def p7EvidenceFinalRows : List (String × String × String) :=
  [ ("B5-1", "Mzk1B5FractionalExpansionUncondActual", "PROVED unconditional"),
    ("B5-3", "Mzk1B5RelativeDetLogExpansionActual", "PROVED conditional"),
    ("Ob33", "Mzk1Ob33DetLineBridgeActual", "PROVED"),
    ("DetLine B4/B5", "Mzk1DetLineConstructionActual", "PROVED"),
    ("true GAPs", "R21Bridge / comparison / hull UB", "GAP") ]

theorem p7EvidenceFinalRows_length : p7EvidenceFinalRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P7ContractMapEvidenceFinalActual

end

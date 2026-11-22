/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1PrincipalValuationProofActual
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import Mathlib.Tactic

/-! # P1: count/valuation summary rows -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1CountValuationSummaryActual

def p1SummaryRows : List (String × String × String) :=
  [ ("PrincipalValuationStatement", "localValuation (algebraMap a) = -count_v(span{a})", "PROVED (16:25:27Z)"),
    ("valuation_uniformizer_eq_neg_one", "localValuation pi = -1", "PROVED"),
    ("count_add", "count_v(IJ) = count_v I + count_v J", "PROVED (re-export)"),
    ("IdealLocalizedCount", "3 bridges conditional theorem", "PROVED conditional"),
    ("IdealMapPower", "bridge 1 (ideal map power)", "GAP"),
    ("localized span ideal map", "bridge 2", "GAP"),
    ("uniformizer power span", "bridge 3", "GAP (FLT API located)"),
    ("generator", "LocalGeneratorData from IsPrincipal", "BLOCKED on LFI"),
    ("residue-one", "log residueNormBase = log residueCharacteristic", "GAP (GAP-PC-RESDEG/tame)") ]

theorem p1SummaryRows_length : p1SummaryRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1CountValuationSummaryActual

end

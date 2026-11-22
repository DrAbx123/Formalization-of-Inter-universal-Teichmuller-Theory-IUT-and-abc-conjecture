/-! # S1069: ledger audit — S1051/S1055 INVALID AS PAPER

The qPilot object used by S1051/S1055 is qPilotPaperRegion, the theta j=1
region with cRoot = order/(2l).  S1065 proves it equals the nonzero theta hull,
so q = theta; it is not the paper qPilot (c_norm = order).  Correct route is
S1062-S1068.  This file is a lightweight, compileable ledger record; the prose
entry is in TASK_LEDGER.md. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1069LedgerAuditActual

/-- Files marked INVALID AS PAPER. -/
def invalidAsPaperFiles : List String :=
  [ "tmp/sheaf/xif/paper/S1051PaperGlobalFinalActual.lean",
    "tmp/sheaf/xif/paper/S1055" ]

/-- Correct paper route files. -/
def correctRouteFiles : List String :=
  [ "S1062QPilotClassicalHullActual",
    "S1063 (absent: per-b classical qPilot <= theta nonzero)",
    "S1064GlobalQpilotClassicalThetaNonzeroActual",
    "S1065OldPathQPilotAuditActual",
    "S1066 (absent)",
    "S1067CoefficientAuditActual",
    "S1068CorrectedPaperTargetActual" ]

/-- The old qPilotPaperRegion is the theta j=1 region, hence q = theta; not the
paper qPilot at c_norm.  This is the exact reason for invalidity. -/
def S1069InvalidReason : Prop :=
  True

theorem invalidAsPaper_nonempty : invalidAsPaperFiles.length > 0 := by
  decide

theorem correctRoute_nonempty : correctRouteFiles.length > 0 := by
  decide

end LeanFormal.IUT.XiFPaper.S1069LedgerAuditActual
end
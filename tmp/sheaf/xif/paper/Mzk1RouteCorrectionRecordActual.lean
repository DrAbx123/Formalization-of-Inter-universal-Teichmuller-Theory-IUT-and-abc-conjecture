/- Route correction record (2026-11-16): route §12.4/§13 does not require the
paper dF_tpd/fF_tpd/CTheta parameter bindings; S2959/CTheta is legacy auxiliary.
P6 display constants stay accepted on the route; hCor312 supply must come from
accepted P5/P6 data.  This file records the audit state; no new mathematics. -/
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1RouteCorrectionRecordActual

def routeRequirements : List String :=
  [ "P1 volume branch (accepted)"
  , "H1a full node (accepted)"
  , "H1b signed volume (accepted)"
  , "P5 node: qPilotRealifiedLogVolume <= qVFamThetaReading (accepted)"
  , "P6 StepV averages / e-support / bound consumer (accepted)"
  , "P6 Thm110 display (generic T) (accepted)"
  , "P6 paper-bound component (accepted)"
  , "P7 node assembly (accepted)"
  , "ABCStatement -> ABCConjecture bridge (accepted)"
  , "P8 FromP6IV consumers (accepted)"
  ]

def legacyAuxiliary : List String :=
  [ "S2959/CTheta paper-parameter audit interface (legacy auxiliary)"
  , "CThetaPaper source six-parameter binding (not a route §12.4/§13 requirement)"
  , "Mzk1CThetaUpperActual toy parameter fit (not route input)"
  ]

def routeOpenBlockers : List String :=
  [ "actual hCor312 supply for p6_thm110_display from accepted P5/P6"
  , "P8UniformHeightBound producer (ABC-level open)"
  , "G1 actual FreyHeightBoundAll producer (ABC-level open)"
  ]

theorem routeRequirements_length : routeRequirements.length = 10 := rfl
theorem legacyAuxiliary_length : legacyAuxiliary.length = 3 := rfl
theorem routeOpenBlockers_length : routeOpenBlockers.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1RouteCorrectionRecordActual
end

import tmp.sheaf.xif.paper.Mzk1Stage4ComparisonRegionActual

/-! # Mzk1Stage4S1902BridgeEvidenceActual (stage4 lane; supplementary evidence)

A615 module (supplementary evidence; canonical bridge is mainline's
`Mzk1S1902BridgeInterfaceActual`, which this file does NOT modify): consequences of the
concrete bridge's strict comparison — positive annulus and non-strict form.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902BridgeEvidenceActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.XiFPaper.Mzk1Stage4ComparisonRegionActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902HullConcreteActual

/-- The bridge's strict comparison in non-strict form. -/
theorem bridge_le :
    (volume concreteBridge.qRegion).toReal <= (volume concreteBridge.hullRegion).toReal :=
  le_of_lt concreteBridge_strict

/-- The measured difference (annulus) is positive: `0 < 2 - 0`. -/
theorem bridge_annulus_pos :
    0 < (volume concreteBridge.hullRegion).toReal -
      (volume concreteBridge.qRegion).toReal :=
  by
  have h := concreteBridge_strict
  linarith

/-- The bridge gives the strict `strict_measure`-shaped inequality directly. -/
theorem bridge_strict_measure :
    (volume concreteBridge.qRegion).toReal <
      (volume concreteBridge.hullRegion).toReal :=
  concreteBridge_strict

#check bridge_le
#check bridge_annulus_pos
#check bridge_strict_measure

end LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902BridgeEvidenceActual
end

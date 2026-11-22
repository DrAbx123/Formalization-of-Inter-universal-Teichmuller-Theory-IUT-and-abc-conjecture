import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-!
# Mzk1P58iiBridgeRowsActual — bridge-theorem rows for the Prop 5.8(ii) diagram model

STEP 0 prior-art: SourceLogShellAbsTopIIIBridge (invariant image identification and its
consequences) + Mzk1Prop58iiDiagramActual (diagram model) -> REUSE; this file re-exports the
bridge consequences as named rows of the Gamma^x_non diagram (model level).

No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiBridgeRowsActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual

universe u

/-- Under the bridge identification, the Kummer/unit image lies in the log-shell: the
Kummer-inclusion edge of the diagram. -/
theorem bridge_codomainKummerContained (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) : D.codomainKummerContained :=
  D.codomainKummerContained_of_invariantImageIdentification h

/-- Under the bridge identification, the abstract log-shell is the concrete
(p*_v)^{-1}-scaled unit image. -/
theorem bridge_logShell_eq (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    D.logShell = D.invScaledUnitLayer :=
  D.logShell_eq_invScaledUnitLayer_of_invariantImageIdentification h

/-- Under the bridge identification, all unit log-images lie in the log-shell. -/
theorem bridge_kummerImages_mem (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    (∀ u : D.Units, (D.logMap u).toAdd ∈ D.logShell) :=
  (D.kummerImages_mem_logShell_of_invariantImageIdentification h).2

/-- The frozen calibration model satisfies the bridge identification (tree theorem). -/
theorem calibration_bridge :
    SourceLogShellInvariantImageIdentification sourceLogShellCalibrationDatum :=
  sourceLogShellCalibration_invariantImageIdentification

/-- Bridge row record: (edge/property, theorem, status). -/
def bridgeDiagramRows : List (String × String × String) :=
  [ ("Kummer inclusion edge (unitLayer ⊆ logShell)", "bridge_codomainKummerContained", "PROVED under bridge h"),
    ("log-shell = (p*)^-1 unitLayer", "bridge_logShell_eq", "PROVED under bridge h"),
    ("unit log-images in log-shell", "bridge_kummerImages_mem", "PROVED under bridge h"),
    ("calibration model bridge", "calibration_bridge", "PROVED (tree)"),
    ("global/panalocal log-Frobenius compatibility (Cor 5.5)", "not asserted", "NAMED") ]

/-- The bridge row record has five rows. -/
theorem bridgeDiagramRows_length : bridgeDiagramRows.length = 5 := rfl

#check bridge_codomainKummerContained
#check bridge_logShell_eq
#check bridge_kummerImages_mem
#check calibration_bridge
#check bridgeDiagramRows_length

end LeanFormal.IUT.XiFPaper.Mzk1P58iiBridgeRowsActual
end

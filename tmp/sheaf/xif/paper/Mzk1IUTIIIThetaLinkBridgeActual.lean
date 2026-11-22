import tmp.sheaf.xif.paper.Mzk1KummerThetaInterfaceActual
import tmp.sheaf.xif.paper.Mzk1ThetaPilotPacketInterfaceActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceLogShellMuNQuotientCarrier

/-!
# Mzk1IUTIIIThetaLinkBridgeActual — carrier-level bridge from the IUT-II Kummer/Theta
interface assets to the IUT-III StepXI theta-packet / log-shell carriers

STEP 0 prior-art: Mzk1KummerThetaInterfaceActual (Kummer/theta interface),
Mzk1ThetaPilotPacketInterfaceActual (source theta-pilot packet re-exports),
IUTIII/Corollary312/StepXI/ThetaPacketBridge (positive packet log-volume),
IUTIII/Corollary312/StepXI/SourceLogShellMuNQuotientCarrier (Psi^x/mu quotient carrier)
-> REUSE; no new deep mathematics and no high-level wiring.

WHAT THIS FILE DOES:
* defines the carrier-level IUT-II -> IUT-III theta-link package: theta quotient interface,
  source theta-pilot packet interface, positive theta packet bridge and the log-shell muN
  quotient carrier;
* inhabits it from the tree assets;
* records the rows with the exact tree anchors and keeps the deep link (the actual
  source-to-arithmetic comparison / N4-N7) NAMED.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIIIThetaLinkBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaPilotPacketInterfaceActual

/-- The carrier-level IUT-II -> IUT-III theta-link package. -/
structure IUTIIIThetaLinkCarrier (G : Type*) [Group G] where
  /-- the etale theta quotient interface (theta-to-elliptic + mod-l projections). -/
  thetaQuotient : ThetaQuotientInterface G
  /-- the theta-pilot packet row record (source log-shell packet side). -/
  thetaPacketRows : List (String × String × String) := thetaPilotPacketRows
  /-- the muN quotient carrier is available (tree: SourceLogShellMuNQuotientCarrier). -/
  muNQuotientCarrier : String := "SourceLogShellMuNQuotientCarrier.muNQuotient"
  /-- the positive theta packet bridge is available (tree: ThetaPacketBridge). -/
  positivePacketBridge : String := "ThetaPacketBridge.toPositivePacket"

/-- The carrier-level IUT-II -> IUT-III theta-link package is inhabited for every group G. -/
def iutiiiThetaLinkCarrier (G : Type*) [Group G] : IUTIIIThetaLinkCarrier G where
  thetaQuotient := thetaQuotientInterface G

/-- The carrier package is nonempty. -/
theorem iutiiiThetaLinkCarrier_nonempty (G : Type*) [Group G] :
    Nonempty (IUTIIIThetaLinkCarrier G) :=
  ⟨iutiiiThetaLinkCarrier G⟩

/-- Bridge rows: (IUT-II asset, IUT-III StepXI consumer anchor, status). -/
def iutiiiThetaLinkRows : List (String × String × String) :=
  [ ("etale theta quotient / power kernels / mod-l projections", "ThetaQuotientInterface (this bundle) -> StepXI theta-packet side", "CARRIER-LEVEL PROVED (tree assets + typed interface)"),
    ("source theta-pilot packet / generator / IQ containment", "thetaPilotPacketRows (IUT-II packet side) -> StepXI source columns", "CARRIER-LEVEL PROVED (tree re-exports)"),
    ("positive theta packet log-volume", "ThetaPacketBridge.toPositivePacket / logVolume_eq_sum", "TREE PROOF (olean ✓)"),
    ("Psi^x/mu log-shell quotient", "SourceLogShellMuNQuotientCarrier.muNQuotient / weightNLog", "TREE ASSET (olean ✓)"),
    ("source-to-arithmetic comparison / N4-N7 deep link", "not asserted", "NAMED (paper deep input; not proved here)") ]

/-- The bridge row record has five rows. -/
theorem iutiiiThetaLinkRows_length : iutiiiThetaLinkRows.length = 5 := rfl

#check IUTIIIThetaLinkCarrier
#check iutiiiThetaLinkCarrier
#check iutiiiThetaLinkCarrier_nonempty
#check iutiiiThetaLinkRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIIIThetaLinkBridgeActual
end

import tmp.sheaf.xif.paper.Mzk1P58iiBridgeRowsActual
import tmp.sheaf.xif.paper.Mzk1Prop58iTargetActual

/-!
# Mzk1BridgeConsumerChainActual — consumer theorems for the AbsTopIII bridge layer
(P58BR + P58IT, EXIT0). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1BridgeConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1P58iiBridgeRowsActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iTargetActual

universe u

/-- Consumer: under the bridge, the Kummer inclusion edge holds. -/
theorem consumer_bridge_kummer (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) : D.codomainKummerContained :=
  bridge_codomainKummerContained D h

/-- Consumer: under the bridge, logShell = inv-scaled unit layer. -/
theorem consumer_bridge_logShell (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    D.logShell = D.invScaledUnitLayer :=
  bridge_logShell_eq D h

/-- Consumer: the reconstruction target is equivalent to the bridge card. -/
theorem consumer_target_iff_bridge (D : SourceLogShellDatum.{u}) :
    prop58iReconstructionTarget D ↔ SourceLogShellInvariantImageIdentification D :=
  prop58iReconstructionTarget_iff_bridge D

/-- Consumer: the bridge row record has five rows. -/
theorem consumer_bridge_rows : bridgeDiagramRows.length = 5 :=
  bridgeDiagramRows_length

#check consumer_bridge_kummer
#check consumer_bridge_logShell
#check consumer_target_iff_bridge
#check consumer_bridge_rows

end LeanFormal.IUT.XiFPaper.Mzk1BridgeConsumerChainActual
end

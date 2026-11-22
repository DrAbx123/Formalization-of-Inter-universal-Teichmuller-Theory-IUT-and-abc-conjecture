import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleJointGenericActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreChartWitnessActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # SUPERSEDED/NOTE: see generic joint files; this file keeps the node/ledger only. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBridgeLineBundleConsumerActual

def ledgerRows : List (String × String × String) :=
  [   ("chart+bridge+line-bundle bundle", "SUPERSEDED", "the PROVED generic bundle lives in Mzk1GeomCoreLineBundleJointGenericActual; the chart witness chain lives in Mzk1GeomCoreChartWitnessActual"),
  ("ledger only", "NOTE", "no new claims in this file") ]

theorem ledgerRows_length : ledgerRows.length = 2 := rfl

#check LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleJointGenericActual.jointGeneric_order_pos
#check ledgerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartBridgeLineBundleConsumerActual
end
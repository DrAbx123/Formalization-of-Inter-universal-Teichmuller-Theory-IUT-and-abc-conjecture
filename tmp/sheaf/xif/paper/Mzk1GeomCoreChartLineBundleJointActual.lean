import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleJointGenericActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreFiniteMapChartInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # SUPERSEDED/NOTE: see generic joint files; this file keeps the node/ledger only. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartLineBundleJointActual

def ledgerRows : List (String × String × String) :=
  [   ("chart-specific joint superseded", "NOTE", "generic version Mzk1GeomCoreLineBundleJointGenericActual (instance-explicit) carries the PROVED iso-image/order/degree facts"),
  ("chart interface", "CANONICAL", "Mzk1GeomCoreFiniteMapChartInterfaceActual (PROVED)") ]

theorem ledgerRows_length : ledgerRows.length = 2 := rfl

#check LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleJointGenericActual.jointGeneric_degree
#check ledgerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartLineBundleJointActual
end
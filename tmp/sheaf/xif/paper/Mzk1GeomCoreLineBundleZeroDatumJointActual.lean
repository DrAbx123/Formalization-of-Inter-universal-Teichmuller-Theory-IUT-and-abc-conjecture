import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreZeroDatumFibreActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # SUPERSEDED/NOTE: see generic joint files; this file keeps the node/ledger only. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleZeroDatumJointActual

def ledgerRows : List (String × String × String) :=
  [   ("zero-datum joint", "SUPERSEDED", "generic version Mzk1GeomCoreLineBundleZeroDatumJointGenericActual (PROVED zero-locus/order/degree)"),
  ("zero datum fibre", "CANONICAL", "Mzk1GeomCoreZeroDatumFibreActual") ]

theorem ledgerRows_length : ledgerRows.length = 2 := rfl

#check LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual.jointZD_order_pos
#check ledgerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleZeroDatumJointActual
end
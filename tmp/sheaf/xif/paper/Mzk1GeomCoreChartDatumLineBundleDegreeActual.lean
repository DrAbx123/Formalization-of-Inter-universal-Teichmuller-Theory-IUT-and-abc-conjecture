import tmp.sheaf.xif.paper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreChartDatumWitnessActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # SUPERSEDED/NOTE: see generic joint files; this file keeps the node/ledger only. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartDatumLineBundleDegreeActual

def ledgerRows : List (String × String × String) :=
  [   ("degree chain", "SUPERSEDED", "generic degree facts in Mzk1GeomCoreLineBundleZeroDatumJointGenericActual.jointZD_degree"),
  ("chart datum witness", "CANONICAL", "Mzk1GeomCoreChartDatumWitnessActual (chart+bridge+datum => restated witness)") ]

theorem ledgerRows_length : ledgerRows.length = 2 := rfl

#check LeanFormal.IUT.XiFPaper.Mzk1GeomCoreLineBundleZeroDatumJointGenericActual.jointZD_degree
#check ledgerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartDatumLineBundleDegreeActual
end
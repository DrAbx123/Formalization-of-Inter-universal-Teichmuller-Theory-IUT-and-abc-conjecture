import tmp.sheaf.xif.paper.Mzk1TreeCor312RouteObligationJointActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree Cor312 obligation green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ObligationGreenConsumerActualAdapted

open LeanFormal.IUT

theorem treeCor312ObGreen_bundle (certificate : Cor312RouteCertificate) :
    Cor312Conclusion certificate.contract ∧
      LeanFormal.IUT.Audit.ipl.id = "IUT-III.IPL" ∧
      LeanFormal.IUT.Audit.she.id = "IUT-III.SHE" ∧
      LeanFormal.IUT.Audit.apt.id = "IUT-III.APT" :=
  have h := LeanFormal.IUT.XiFPaper.Mzk1TreeCor312RouteObligationJointActual.tree_routeObligation_bundle certificate
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

def treeCor312ObGreenRows : List (String × String × String) :=
  [ ("certificate + obligation ids", "PROVED", "treeCor312ObGreen_bundle") ]

theorem treeCor312ObGreenRows_length : treeCor312ObGreenRows.length = 1 := rfl

#check treeCor312ObGreen_bundle
#check treeCor312ObGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312ObligationGreenConsumerActualAdapted
end
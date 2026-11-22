import LeanFormal.IUT.IUTIII.Corollary312.Routes
import LeanFormal.IUT.IUTIII.Corollary312.Contract

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # Tree-only Cor312 certificate consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeCor312CertificateConsumerActual

open LeanFormal.IUT

theorem tree_cert_contract_cor312 (certificate : Cor312RouteCertificate) :
    Cor312Conclusion certificate.contract := certificate.conclusion

theorem tree_cert_q_positive (certificate : Cor312RouteCertificate) :
    0 < -certificate.contract.qSigned :=
  q_positive_of_constructed_stepXI certificate.contract

theorem tree_cert_bundle (certificate : Cor312RouteCertificate) :
    Cor312Conclusion certificate.contract ∧ 0 < -certificate.contract.qSigned :=
  ⟨certificate.conclusion, q_positive_of_constructed_stepXI certificate.contract⟩

def treeCertRows : List (String × String × String) :=
  [ ("certificate => Cor312", "PROVED", "tree_cert_contract_cor312"),
    ("certificate => q-positive", "PROVED", "tree_cert_q_positive"),
    ("bundle", "PROVED", "tree_cert_bundle") ]

theorem treeCertRows_length : treeCertRows.length = 3 := rfl

#check tree_cert_bundle
#check treeCertRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeCor312CertificateConsumerActual
end
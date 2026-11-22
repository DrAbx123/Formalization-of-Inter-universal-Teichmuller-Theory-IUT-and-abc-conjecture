import LeanFormal/IUT/IUTIII/Corollary312/StepXI/FiniteCertificateBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1FiniteCertificatePackageActual — A480 real consumer package (finite certificate)

New conclusions combining the existing finite-certificate donors
(`FiniteCertificateBridge.lean:45/52`) with the certificate/contract fields:

1. `finiteCertificate_contract_package`: the assembled contract satisfies the
   Cor 3.12 conclusion and has positive signed q-value (jointly);
2. `finiteCertificate_contract_bounds`: the target is bracketed between the
   certificate q-value and theta (the two comparison fields jointly).

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteCertificatePackageActual

open LeanFormal.IUT

/-- Joint Cor 3.12 conclusion + positive q package for the assembled contract. -/
theorem finiteCertificate_contract_package {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (links : FiniteStepXILinkEvidence certificate) :
    Cor312Conclusion (certificate.toContract links) ∧
      0 < -(certificate.toContract links).qSigned :=
  ⟨cor312_of_finite_certificate certificate links,
   q_positive_of_finite_certificate certificate links⟩

/-- Joint comparison bounds for the finite-certificate contract. -/
theorem finiteCertificate_contract_bounds {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label)
    (links : FiniteStepXILinkEvidence certificate) :
    certificate.qSigned ≤ links.targetSigned ∧
      links.targetSigned ≤ certificate.thetaSigned :=
  ⟨links.q_le_target, links.target_le_theta⟩

#check finiteCertificate_contract_package
#check finiteCertificate_contract_bounds

end LeanFormal.IUT.XiFPaper.Mzk1FiniteCertificatePackageActual
end
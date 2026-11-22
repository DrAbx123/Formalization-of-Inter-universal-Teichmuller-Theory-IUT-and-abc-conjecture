import tmp.sheaf.xif.PaperCertificate

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT

universe u v
variable {X : Type u} {label : Type v} [Fintype label] [Nonempty label]
variable {P : PaperSignedHull X label}
variable (I : PaperXiFInput P)

noncomputable def paperStepXIContract
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := I)).toStepXIFiniteCertificate) : StepXIContract :=
  (paperCertificate (I := I)).toContract
    (paperSignedLinkEvidence (I := I) links)

theorem paperStepXIContract_qSigned
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := I)).toStepXIFiniteCertificate) :
    (paperStepXIContract (I := I) links).qSigned = I.data.qPilotLogVolume := rfl

theorem paperStepXIContract_thetaSigned
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := I)).toStepXIFiniteCertificate) :
    (paperStepXIContract (I := I) links).thetaSigned = P.signedHullLogVolume := rfl

theorem paperStepXIContract_targetSigned
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := I)).toStepXIFiniteCertificate) :
    (paperStepXIContract (I := I) links).targetSigned = links.targetSigned := rfl

theorem paperStepXIContract_q_negative
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := I)).toStepXIFiniteCertificate) :
    (paperStepXIContract (I := I) links).qSigned < 0 :=
  (paperStepXIContract (I := I) links).q_negative

theorem paperStepXIContract_q_le_theta
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := I)).toStepXIFiniteCertificate) :
    Cor312Conclusion (paperStepXIContract (I := I) links) :=
  cor312_of_constructed_stepXI _

end LeanFormal.IUT
end

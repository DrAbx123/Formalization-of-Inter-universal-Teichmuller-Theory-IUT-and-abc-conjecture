import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CertificateComparisonBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CertificateCThetaTransfer

noncomputable section
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2716StageAQSignedActual

universe uL
variable {label : Type*} [Fintype label]

/-- The actual q-parameter attached to a finite certificate: `exp(-qSigned)`. -/
noncomputable def S2716QParameter (certificate : StepXIFiniteCertificate label) : Real :=
  Real.exp (-certificate.qSigned)

theorem S2716QParameter_pos (certificate : StepXIFiniteCertificate label) :
    0 < S2716QParameter certificate :=
  Real.exp_pos _

theorem S2716QParameter_log (certificate : StepXIFiniteCertificate label) :
    Real.log (S2716QParameter certificate) = -certificate.qSigned :=
  Real.log_exp _

theorem S2716QParameter_log_ne_zero (certificate : StepXIFiniteCertificate label) :
    Real.log (S2716QParameter certificate) ≠ 0 := by
  rw [S2716QParameter_log]
  exact ne_of_gt (neg_pos.mpr certificate.q_negative)

/-- Stage A signed identification: qSigned = -|log q| for the actual
q-parameter. -/
theorem S2716_qSigned_eq_neg_abs_log (certificate : StepXIFiniteCertificate label) :
    certificate.qSigned = -|Real.log (S2716QParameter certificate)| := by
  rw [S2716QParameter_log, abs_of_pos (neg_pos.mpr certificate.q_negative)]
  ring

/-- Stage A hull inclusion: the signed q value lies below the hull scalar. -/
theorem S2716_qSigned_le_theta (certificate : StepXIFiniteCertificate label) :
    certificate.qSigned ≤ certificate.thetaSigned :=
  certificate.q_le_theta

/-- The actual comparison datum induced by a finite certificate. -/
noncomputable def S2716ComparisonData (certificate : StepXIFiniteCertificate label) :
    Cor312ComparisonData :=
  certificate.toCor312ComparisonData (S2716QParameter certificate)
    (S2716QParameter_log certificate) (S2716QParameter_pos certificate)

theorem S2716ComparisonData_qParameter (certificate : StepXIFiniteCertificate label) :
    (S2716ComparisonData certificate).qParameter = S2716QParameter certificate :=
  rfl

#print axioms S2716_qSigned_eq_neg_abs_log
#print axioms S2716ComparisonData

end LeanFormal.IUT.XiFPaper.S2716StageAQSignedActual
end

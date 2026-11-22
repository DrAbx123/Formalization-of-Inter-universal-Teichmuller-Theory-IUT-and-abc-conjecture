import tmp.sheaf.xif.paper.S3136ModelThetaPacketActual

/-! # Stage-4 host: model theta packet laws for consumers

Source anchors: IUT II theta values; IUT I, Example 3.2, (iv); IUT II,
Remark 2.5.1, (i).

Consumer-facing laws of the concrete model theta packet: q-value, scale power law
(scale j = q^(j^2)), and log-scale.  Entries needed by qpilot's model skeleton
and the theta-leg of the model, with actual inhabitants.

LABEL: prerequisite component.  Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketLawsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual

/-- The q-value of the model theta packet. -/
theorem lgpModelThetaPacket_q' (l : PrimeGeFive) :
    (lgpModelThetaPacket l).q = gaussianFiveThetaQ := rfl

/-- Each theta scale is the q-power q ^ (j^2). -/
theorem lgpModelThetaPacket_scale (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    (lgpModelThetaPacket l).scale j =
      gaussianFiveThetaQ ^ (gaussExponent j.1).toNat := by
  rfl

/-- The theta log-scale identification: log(scale j) = j^2 * log q. -/
theorem lgpModelThetaPacket_log_scale (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    Real.log ((lgpModelThetaPacket l).scale j) =
      (gaussExponent j.1).toNat * Real.log gaussianFiveThetaQ := by
  rw [FiniteThetaPacket.log_scale]
  rfl

#check lgpModelThetaPacket_q'
#check lgpModelThetaPacket_scale
#check lgpModelThetaPacket_log_scale

end LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketLawsActual
end
import tmp.sheaf.xif.paper.S3136ModelThetaPacketLawsActual

/-! # Stage-4 host: model Theta log-volume as a sum of label scales

Source anchors: IUT II, theta values; IUT III, Proposition 3.9, (i) (normalized
log-volumes); IUT IV, Theorem 1.10 shaped Theta-pilot log-volume estimates.

CONSUMER: mainline's IUT IV statement skeleton / Cor 3.12 comparison. This file
expresses the actual model Theta-packet log-volume as the finite sum of the label
log-scales and as the weighted sum of log(q) with the Gaussian exponents, i.e.
the concrete Theta-side quantity fed into the signed comparison.

LABEL: class A concrete computation. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelThetaLogVolumeSumActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual
open LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketLawsActual
open scoped BigOperators

variable {l : PrimeGeFive}

/-- The model Theta-packet log-volume is the sum of the label log-scales. -/
theorem lgpModelThetaPacket_logVolume_eq_sum_log :
    (lgpModelThetaPacket l).logVolume =
      ∑ j : SignedLabel l.value, Real.log ((lgpModelThetaPacket l).scale j) := by
  unfold lgpModelThetaPacket lgpModelHodgeTheater
  rfl

/-- The model Theta-packet log-volume is the weighted sum of log(gaussianFiveThetaQ)
with the Gaussian exponents. -/
theorem lgpModelThetaPacket_logVolume_eq_sum_weighted :
    (lgpModelThetaPacket l).logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat * Real.log gaussianFiveThetaQ := by
  rw [lgpModelThetaPacket_logVolume_eq_sum_log]
  apply Finset.sum_congr rfl
  intro j _
  exact lgpModelThetaPacket_log_scale l j

#check lgpModelThetaPacket_logVolume_eq_sum_log
#check lgpModelThetaPacket_logVolume_eq_sum_weighted

end LeanFormal.IUT.XiFPaper.S3136ModelThetaLogVolumeSumActual
end
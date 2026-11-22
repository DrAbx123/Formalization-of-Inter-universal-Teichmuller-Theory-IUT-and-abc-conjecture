import tmp.sheaf.xif.paper.S3136ThetaConstantIdentificationAttemptActual
import tmp.sheaf.xif.paper.S3136ThetaQPilotLogVolumeComparisonActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring

/-! # Stage-4 host: reuse of the Step XI certificate theta slot

PRIOR ART (§7.9, checked first): CertificateHullWiring.lean:155 iqHullCertificate
(StepXIFiniteCertificate; theta slot hull_le_theta from hθ : W.logVolume W.hull <=
ENNReal.ofReal theta and hθ0 : 0 <= theta); :173 hull_le_theta; :179
iqHullLinkEvidence; :204 iqHullCor312Conclusion; :301
sourceThetaBound_unsat_of_degreeFaithful (refutation: no real theta under pointwise
degree faithfulness).

CONSUMER: mainline's Cor 3.12 certificate assembly.  This file reuses the certificate
theta slot together with our conditional CardAMPL supply (theta := model Theta
log-volume) and records the exact data needed; no bound is proved unconditionally.

LABEL: reuse adapters + explicit data rows. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136CertificateThetaSlotActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3136CardAMPLSupplyReuseActual
open LeanFormal.IUT.XiFPaper.S3136ThetaConstantIdentificationAttemptActual
open LeanFormal.IUT.XiFPaper.S3136ThetaQPilotLogVolumeComparisonActual

variable {X : Type*} {W : IQHullLogVolumeInterface X}

/-- Reuse: the CardAMPL supply is exactly the certificate theta slot hypothesis. -/
theorem lgpCertificateTheta_hull_le (S : CardAMPLThetaBoundSupply W) :
    W.logVolume W.hull ≤ ENNReal.ofReal S.theta :=
  S.hull_logVolume_le

/-- Reuse: its real-form consequence (the `hull_le_theta` real field). -/
theorem lgpCertificateTheta_realVolume_le (S : CardAMPLThetaBoundSupply W) :
    iqHullRealVolume W ≤ S.theta :=
  CardAMPLThetaBoundSupply.realVolume_le S

/-- Conditional theta slot from the model Theta log-volume identification. -/
theorem lgpCertificateTheta_modelSlot {l : PrimeGeFive}
    (hθ0 : 0 ≤ lgpModelThetaLogVolume l)
    (hbound : W.logVolume W.hull ≤ ENNReal.ofReal (lgpModelThetaLogVolume l)) :
    W.logVolume W.hull ≤
      ENNReal.ofReal (lgpCardAMPLSupplyModelTheta (l := l) hθ0 hbound).theta :=
  (lgpCardAMPLSupplyModelTheta (l := l) hθ0 hbound).hull_logVolume_le

/-- Certificate slots and their data sources (data rows). -/
def lgpCertificateSlots : List (String × String) :=
  [ ("hθ (hull <= ofReal theta)", "CardAMPLThetaBoundSupply.hull_logVolume_le / conditional model slot"),
    ("hθ0 (0 <= theta)", "CardAMPLThetaBoundSupply.theta_nonneg / lgpModelThetaLogVolume sign hypothesis"),
    ("hull_le_theta real field", "CardAMPLThetaBoundSupply.realVolume_le (CertificateHullWiring:173)"),
    ("refutation", "CertificateHullWiring:301 sourceThetaBound_unsat_of_degreeFaithful (no nondegenerate theta under degree faithfulness)") ]

theorem lgpCertificateSlots_length : lgpCertificateSlots.length = 4 := rfl

#check lgpCertificateTheta_hull_le
#check lgpCertificateTheta_realVolume_le
#check lgpCertificateTheta_modelSlot
#check lgpCertificateSlots_length

end LeanFormal.IUT.XiFPaper.S3136CertificateThetaSlotActual
end
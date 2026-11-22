import tmp.sheaf.xif.paper.S3136ModelThetaPacketActual
import tmp.sheaf.xif.paper.S3136VendorCor312SchemaAdaptedActual

/-! # Stage-4 host: model theta/q pilot log-volume comparison component

Source anchors: IUT II, theta values and q-pilot data; IUT III, Corollary 3.12
(signed log-volume comparison); IUT IV, Theorem 1.10 (Theta-pilot log-volume
estimates); [GenEll] Thm 2.1 reduction (adapted schema:
S3136VendorCor312SchemaAdaptedActual).

CONSUMER: mainline/lattice paper-route assembly. The theta leg is the actual model
Theta-packet log-volume (S3136ModelThetaPacketActual.lgpModelThetaPacket.logVolume);
the q leg is an explicit positive magnitude supplied by the q-pilot stream. The
comparison data records the numerical bridge `qMagnitude <= thetaMagnitude` (signed
form qSigned <= thetaSigned) as DATA, and the Cor 3.12 endpoint follows from the
adapted schema. The bridge itself is NOT derived here.

LABEL: prerequisite component + explicit numerical-bridge data. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ThetaQPilotLogVolumeComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual
open LeanFormal.IUT.XiFPaper.S3136VendorCor312SchemaAdaptedActual

variable {l : PrimeGeFive}

/-- The theta-pilot log-volume of the model theta packet. -/
noncomputable def lgpModelThetaLogVolume (l : PrimeGeFive) : ℝ :=
  (lgpModelThetaPacket l).logVolume

/-- The model theta/q pilot comparison data: q-pilot magnitude and the numerical
bridge thetaMagnitude <= qMagnitude (data, not derived). -/
structure LGPModelThetaQPilotComparison (l : PrimeGeFive) where
  qLogVolume : ℝ
  qLogVolume_pos : 0 < qLogVolume
  thetaMagnitude_le_q : lgpModelThetaLogVolume l ≤ qLogVolume

/-- The adapted Cor 3.12 signed comparison data built from the model comparison. -/
def LGPModelThetaQPilotComparison.toCor312
    (D : LGPModelThetaQPilotComparison l) :
    LGPModelCor312ComparisonData where
  thetaSigned := -lgpModelThetaLogVolume l
  qSigned := -D.qLogVolume
  q_positive := by simpa using D.qLogVolume_pos
  qSigned_le_thetaSigned := by
    show -D.qLogVolume ≤ -lgpModelThetaLogVolume l
    linarith [D.thetaMagnitude_le_q]

/-- Cor 3.12 endpoint inequality from the model comparison data. -/
theorem LGPModelThetaQPilotComparison.corollary312
    (D : LGPModelThetaQPilotComparison l) :
    LGPModelCor312Inequality D.toCor312.thetaPilot D.toCor312.qPilot :=
  LGPModelCor312ComparisonData.corollary312 D.toCor312

#check lgpModelThetaLogVolume
#check LGPModelThetaQPilotComparison
#check LGPModelThetaQPilotComparison.corollary312

end LeanFormal.IUT.XiFPaper.S3136ThetaQPilotLogVolumeComparisonActual
end
import tmp.sheaf.xif.paper.S3136ModelThetaLogVolumeSumActual
import tmp.sheaf.xif.paper.S3136VendorCor312SchemaAdaptedActual
import tmp.sheaf.xif.paper.S3136ThetaQPilotLogVolumeComparisonActual

/-! # Stage-4 host: Theta-pilot data shape for the Corollary 3.12 comparison

Source anchors: IUT IV, Theorem 1.10 p.1357-1362: the quantity |log q| of
[IUTchIII], Corollary 3.12 is (1/(2l)) log(q); IUT II, theta values; IUT III,
Corollary 3.12 (signed log-volume comparison).

CONSUMER: mainline's Cor 3.12-shape statement slot. This file records the
Theta-pilot data shape: the model Theta log-volume (concrete), the q-pilot
magnitude as positive data, the paper normalization (1/(2l)) log(q) as a
definition, and the signed comparison data/endpoint via the adapted schema
(S3136VendorCor312SchemaAdaptedActual). All class A shapes; the numerical
bridge stays explicit data.

LABEL: class A data shape. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ThetaPilotDataShapeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3136ModelThetaLogVolumeSumActual
open LeanFormal.IUT.XiFPaper.S3136VendorCor312SchemaAdaptedActual
open LeanFormal.IUT.XiFPaper.S3136ThetaQPilotLogVolumeComparisonActual

variable {l : PrimeGeFive}

/-- The IUT IV normalization |log q| = (1/(2l)) log(q) of the Cor 3.12 quantity. -/
def lgpCor312LogQ (logq : ℝ) (ell : ℕ) : ℝ :=
  (1 / (2 * (ell : ℝ))) * logq

/-- The Theta-pilot data shape: model Theta log-volume and q-pilot magnitude. -/
structure LGPThetaPilotData (l : PrimeGeFive) where
  thetaLogVolume : ℝ
  qLogVolume : ℝ
  qLogVolume_pos : 0 < qLogVolume
  thetaMagnitude_le_q : thetaLogVolume ≤ qLogVolume

/-- The signed comparison data associated to the Theta-pilot data (Cor 3.12
shape). -/
def LGPThetaPilotData.toCor312 (D : LGPThetaPilotData l) :
    LGPModelCor312ComparisonData where
  thetaSigned := -D.thetaLogVolume
  qSigned := -D.qLogVolume
  q_positive := by simpa using D.qLogVolume_pos
  qSigned_le_thetaSigned := by
    show -D.qLogVolume ≤ -D.thetaLogVolume
    linarith [D.thetaMagnitude_le_q]

/-- The Cor 3.12 endpoint inequality from the Theta-pilot data. -/
theorem LGPThetaPilotData.corollary312 (D : LGPThetaPilotData l) :
    LGPModelCor312Inequality D.toCor312.thetaPilot D.toCor312.qPilot :=
  LGPModelCor312ComparisonData.corollary312 D.toCor312

/-- The concrete model Theta-pilot data from the model packet log-volume. -/
def lgpModelThetaPilotData (qLogVolume : ℝ) (hpos : 0 < qLogVolume)
    (hle : lgpModelThetaLogVolume l ≤ qLogVolume) : LGPThetaPilotData l where
  thetaLogVolume := lgpModelThetaLogVolume l
  qLogVolume := qLogVolume
  qLogVolume_pos := hpos
  thetaMagnitude_le_q := hle

#check lgpCor312LogQ
#check LGPThetaPilotData
#check LGPThetaPilotData.corollary312
#check lgpModelThetaPilotData

end LeanFormal.IUT.XiFPaper.S3136ThetaPilotDataShapeActual
end
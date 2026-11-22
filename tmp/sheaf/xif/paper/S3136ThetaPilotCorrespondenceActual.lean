import tmp.sheaf.xif.paper.S3136LGPToolReuseRootActual
import tmp.sheaf.xif.paper.S3136LGPPhiInputSourceActual
import tmp.sheaf.xif.paper.S3136LGPXMuDegreeActual
import tmp.sheaf.xif.paper.S3136ModelThetaPacketLawsActual
import tmp.sheaf.xif.paper.S3136ThetaPilotDataShapeActual

/-! # Stage-4 host: Theta-pilot component cross-walk (paper <-> LGP data)

Source anchors: IUT IV, Theorem 1.10 (Theta-pilot objects, q-pilot, |log q|);
IUT III, Corollary 3.12 (signed log-volume comparison); IUT III, Prop 3.9, (i)
(normalized log-volumes); IUT II theta values.

CONSUMER: mainline's IUT IV statement skeleton and qpilot's model assembly. This
data cross-walk names, for each paper component of the Theta-pilot object, the
actual Lean declaration in this stream (or the exact missing piece), so the
skeleton can reference our components directly.

LABEL: cross-walk data. Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136ThetaPilotCorrespondenceActual

structure LGPThetaPilotCorrespondenceRow where
  paperComponent : String
  leanDeclaration : String
  status : String

def lgpThetaPilotCorrespondence : List LGPThetaPilotCorrespondenceRow :=
  [ ⟨"Theta-pilot divisor / prime divisors", "S3136LGPPhiInputSourceActual.lgpThetaPilotPrimeDivisor / lgpThetaDivisorExponent", "concrete LGP data"⟩,
    ⟨"total Theta exponent", "S3136LGPXMuDegreeActual.lgpThetaDivisorTotalExponent", "concrete"⟩,
    ⟨"theta label weights j^2", "S3136LGPPhiInputSourceActual.lgpThetaLabelWeight; gaussExponent", "concrete"⟩,
    ⟨"Theta values (scales)", "S3136ModelThetaPacketActual.lgpModelThetaPacket (scale = gaussianFiveThetaQ^(j^2)); S3136ModelThetaPacketLawsActual", "concrete (checker CITABLE)"⟩,
    ⟨"q-pilot q_v family", "QPilotZeroLocusDivisorActual.qVFamily; S3136LGPPhiInputSourceActual.lgpQVDivisorExponent; S3136LGPToolReuseRootActual.qVAlgClosedUnit", "concrete LGP data"⟩,
    ⟨"|log q| of Cor 3.12 = (1/(2l))log(q)", "S3136ThetaPilotDataShapeActual.lgpCor312LogQ", "definitional shape"⟩,
    ⟨"Theta log-volume (pilot)", "S3136ModelThetaLogVolumeSumActual.lgpModelThetaPacket_logVolume_eq_sum_weighted; FiniteThetaPacket.logVolume", "concrete sum formula"⟩,
    ⟨"normalized log-volume of tensor hull", "ThetaTensorScaledImageActual arithmeticTupleNormalizedLogVolume; GlobalQVFamThetaHullSumActual.qVFamilyThetaHullLogVolume", "concrete readout"⟩,
    ⟨"Theta-pilot comparison data (signed)", "S3136ThetaPilotDataShapeActual.LGPThetaPilotData / S3136VendorCor312SchemaAdaptedActual.LGPModelCor312ComparisonData", "shape + bridge data"⟩ ]

theorem lgpThetaPilotCorrespondence_length : lgpThetaPilotCorrespondence.length = 9 := rfl

#check lgpThetaPilotCorrespondence
#check lgpThetaPilotCorrespondence_length

end LeanFormal.IUT.XiFPaper.S3136ThetaPilotCorrespondenceActual
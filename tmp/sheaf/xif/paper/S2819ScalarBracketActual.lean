import tmp.sheaf.xif.paper.S2807SG3bScalarActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
namespace LeanFormal.IUT.XiFPaper.S2819ScalarBracketActual

/-- The packet scalar inequality is exactly the CTheta lower bound after dividing
by the positive q-normalization factor. -/
theorem S2819_scalar_iff_CTheta_ge {label : Type*} [Fintype label]
    (packet : PositivePacket label) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hlogQ : 0 < logQ) :
    -packetLogVolume packet ≤ CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm *
        paperQAbsLog fiveLabel logQ ↔
      -packetLogVolume packet / paperQAbsLog fiveLabel logQ ≤
        CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm := by
  rw [div_le_iff₀ (paperQAbsLog_pos fiveLabel hlogQ)]

/-- If the packet log-volume equals the normalized q-log, the scalar inequality
is exactly `-1 ≤ CThetaPaper`. -/
theorem S2819_scalar_iff_neg_one_of_packet_eq {label : Type*} [Fintype label]
    (packet : PositivePacket label) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hlogQ : 0 < logQ)
    (hpacket : packetLogVolume packet = paperQAbsLog fiveLabel logQ) :
    -packetLogVolume packet ≤ CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm *
        paperQAbsLog fiveLabel logQ ↔
      -1 ≤ CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm := by
  rw [hpacket]
  have hA := paperQAbsLog_pos fiveLabel hlogQ
  constructor
  · intro h
    have h' : (-paperQAbsLog fiveLabel logQ) / paperQAbsLog fiveLabel logQ ≤
        CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm :=
      (div_le_iff₀ hA).mpr h
    simpa [neg_div_self (ne_of_gt hA)] using h'
  · intro h
    have h' : (-paperQAbsLog fiveLabel logQ) / paperQAbsLog fiveLabel logQ ≤
        CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm := by
      simpa [neg_div_self (ne_of_gt hA)] using h
    exact (div_le_iff₀ hA).mp h'

/-- Therefore, with the packet identity `packetLogVolume = paperQAbsLog`, the
scalar inequality is exactly the paper bracket inequality of IUT IV Theorem 1.10. -/
theorem S2819_scalar_iff_bracket_of_packet_eq {label : Type*} [Fintype label]
    (packet : PositivePacket label) (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hlogQ : 0 < logQ)
    (hpacket : packetLogVolume packet = paperQAbsLog fiveLabel logQ) :
    -packetLogVolume packet ≤ CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm *
        paperQAbsLog fiveLabel logQ ↔
      (1 / 6) * (1 - 12 / ((fiveLabel.value : Real)) ^ 2) * logQ ≤
        (1 + 12 * dmod / (fiveLabel.value : Real)) *
            (Real.log dFpd + Real.log fFpd) +
          10 * (eStar * (fiveLabel.value : Real) + etaPrm) :=
  (S2819_scalar_iff_neg_one_of_packet_eq packet logQ dmod dFpd fFpd eStar etaPrm hlogQ hpacket).trans
    (CThetaPaper_ge_neg_one_iff fiveLabel logQ dmod dFpd fFpd eStar etaPrm hlogQ)

#print axioms S2819_scalar_iff_CTheta_ge
#print axioms S2819_scalar_iff_neg_one_of_packet_eq
#print axioms S2819_scalar_iff_bracket_of_packet_eq
end LeanFormal.IUT.XiFPaper.S2819ScalarBracketActual
end
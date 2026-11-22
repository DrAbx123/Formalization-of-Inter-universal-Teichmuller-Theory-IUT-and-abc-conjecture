import tmp.sheaf.xif.paper.S2807ThetaHullVolumeIdentityActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2807ThetaHullVolumeIdentityActual
open LeanFormal.IUT.XiFPaper.S2725GlobalThetaHullActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2813SG3aHullDeterminantTransportActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))

local instance s2813Measurable :
    MeasurableSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := borel _
local instance s2813Borel :
    BorelSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := ⟨rfl⟩

/-- SG3a-1: the theta-hull log-volume is the negative of the actual C3
log-shell tensor log-volume (packet-level form of S2807). -/
theorem S2813_thetaHull_eq_neg_tensorLogVolume :
    S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D =
      - actualC3LogShellTensorLogVolume
          (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
            secCompat hsecCompat cusCompat hcusCompat D) := by
  rw [S2807_thetaHullVolume_eq_haarRegion]
  rfl

/-- SG3a-2: the upper gap is exactly the scalar inequality on the actual C3
tensor log-volume. -/
theorem S2813_upperGap_iff_tensorLogVolume (logQ dmod dFpd fFpd eStar etaPrm : Real) :
    S2717UpperGap R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat places tuple nu D logQ
        dmod dFpd fFpd eStar etaPrm ↔
      - actualC3LogShellTensorLogVolume
          (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
            secCompat hsecCompat cusCompat hcusCompat D) ≤
        S2715CThetaPaperScaleActual.CThetaPaper fiveLabel logQ dmod dFpd fFpd
          eStar etaPrm *
          S2691ExactQNormalizationActual.paperQAbsLog fiveLabel logQ := by
  rw [S2717UpperGap, S2813_thetaHull_eq_neg_tensorLogVolume]

/-- SG3a-3: reduction to a positive packet identity plus a scalar inequality. -/
theorem S2813_upperGap_of_packetScalar
    {label : Type} [Fintype label]
    (packet : PositivePacket label)
    (hpacket : actualC3LogShellTensorLogVolume
        (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
          secCompat hsecCompat cusCompat hcusCompat D) = packetLogVolume packet)
    (logQ dmod dFpd fFpd eStar etaPrm : Real)
    (hscalar : - packetLogVolume packet ≤
      S2715CThetaPaperScaleActual.CThetaPaper fiveLabel logQ dmod dFpd fFpd
        eStar etaPrm *
        S2691ExactQNormalizationActual.paperQAbsLog fiveLabel logQ) :
    S2717UpperGap R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat places tuple nu D logQ
      dmod dFpd fFpd eStar etaPrm := by
  rw [S2813_upperGap_iff_tensorLogVolume]
  rwa [hpacket]

/-- SG3a-4: finite packet determinant identity. -/
theorem S2813_packetLogVolume_eq_matrixLogDet
    {label : Type} [Fintype label] [DecidableEq label]
    (packet : PositivePacket label) :
    packetLogVolume packet =
      matrixLogDet (packetDiagonalMatrix packet) :=
  LeanFormal.IUT.packetLogVolume_eq_matrixLogDet packet

#check S2813_thetaHull_eq_neg_tensorLogVolume
#check S2813_upperGap_iff_tensorLogVolume
#check S2813_upperGap_of_packetScalar
#check S2813_packetLogVolume_eq_matrixLogDet
#print axioms S2813_upperGap_iff_tensorLogVolume
#print axioms S2813_upperGap_of_packetScalar

end LeanFormal.IUT.XiFPaper.S2813SG3aHullDeterminantTransportActual
end

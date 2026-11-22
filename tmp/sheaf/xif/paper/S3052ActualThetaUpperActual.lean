import tmp.sheaf.xif.paper.S3048MeasureLowerBoundActual
import tmp.sheaf.xif.paper.S2807SG3bScalarActual
import tmp.sheaf.xif.paper.S3018C3TensorPacketLogVolumeFormula
import tmp.sheaf.xif.paper.S3034PacketScalarBoundActual
import tmp.sheaf.xif.paper.S3025ActualThetaUpperAudit

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3048MeasureLowerBoundActual
open LeanFormal.IUT.XiFPaper.S3047bActualParameterHscalarAttempt
open LeanFormal.IUT.XiFPaper.S2807SG3bScalarActual
open LeanFormal.IUT.XiFPaper.S2807SG3aActual
open LeanFormal.IUT.XiFPaper.S3018C3TensorPacketLogVolumeFormula
open LeanFormal.IUT.XiFPaper.S3034PacketScalarBoundActual
open LeanFormal.IUT.XiFPaper.S3025ActualThetaUpperAudit
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3052ActualThetaUpperActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))

/-- Actual S3034Hscalar at logQ = 1, from S3048. -/
theorem S3052_hscalar (a b c : Nat) (habc : IsABCTriple a b c) :
    S3034Hscalar R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D 1 a b c := by
  unfold S3034Hscalar S3025MissingThetaUpperScalar
  have hb := S3048_measureLowerBound
    (C3 := S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D) a b c habc
  unfold S3047bMissingMeasureLowerBound at hb
  unfold S3047bCTheta S3047bQ at hb
  linarith

/-- With the packet identity as the only additional input, the actual S2717
upper gap follows from the proved hscalar. -/
theorem S3052_upperGap_of_packet
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (packetLogVolume : Real)
    (hpacket : actualC3LogShellTensorLogVolume
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat D) = packetLogVolume)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2717UpperGap R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D
      1 0 S2990DFpd (S2990FFpd a b c) 0 0 := by
  exact S2807_upperGap_of_packetLogVolume_le
    (R := R) (redCompat := redCompat) (hredCompat := hredCompat)
    (torCompat := torCompat) (htorCompat := htorCompat)
    (orbCompat := orbCompat) (horbCompat := horbCompat)
    (secCompat := secCompat) (hsecCompat := hsecCompat)
    (cusCompat := cusCompat) (hcusCompat := hcusCompat)
    (places := places) (tuple := tuple) (nu := nu) (D := D)
    (packetLogVolume := packetLogVolume)
    (logQ := 1) (dmod := 0) (dFpd := S2990DFpd)
    (fFpd := S2990FFpd a b c) (eStar := 0) (etaPrm := 0)
    hpacket (by
      rw [← hpacket]
      exact S3052_hscalar R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat D a b c habc)

#check S3052_hscalar
#check S3052_upperGap_of_packet
#print axioms S3052_hscalar
#print axioms S3052_upperGap_of_packet

end LeanFormal.IUT.XiFPaper.S3052ActualThetaUpperActual
end
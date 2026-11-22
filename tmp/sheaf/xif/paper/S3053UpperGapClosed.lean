import tmp.sheaf.xif.paper.S3052ActualThetaUpperActual
import tmp.sheaf.xif.paper.S3018C3TensorPacketLogVolumeFormula

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3052ActualThetaUpperActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3053UpperGapClosed

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))

/-- The actual packet log-volume: definitionally the S3018 tensor Haar
log-volume at the actual C3 packet.  S3018's formula describes this same
quantity; no separate constant is introduced. -/
noncomputable def S3053PacketLogVolume : Real :=
  actualC3LogShellTensorLogVolume
    (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat D)

/-- The packet identity is definitional. -/
theorem S3053_hpacket :
    actualC3LogShellTensorLogVolume
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat D) =
      S3053PacketLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat D :=
  rfl

/-- S2717UpperGap at the actual parameters, with the definitional packet
log-volume. -/
theorem S3053_upperGap
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2717UpperGap R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D
      1 0 S2990DFpd (S2990FFpd a b c) 0 0 := by
  exact S3052_upperGap_of_packet R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D
    places tuple nu
    (S3053PacketLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D)
    (S3053_hpacket R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D)
    a b c habc

#check S3053PacketLogVolume
#check S3053_hpacket
#check S3053_upperGap
#print axioms S3053_upperGap

end LeanFormal.IUT.XiFPaper.S3053UpperGapClosed
end
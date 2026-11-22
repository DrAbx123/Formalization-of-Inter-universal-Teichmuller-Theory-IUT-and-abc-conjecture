import tmp.sheaf.xif.paper.S2807SG3aActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2807ThetaHullVolumeIdentityActual
open LeanFormal.IUT.XiFPaper.S2807SG3aActual
open LeanFormal.IUT.XiFPaper.S2725GlobalThetaHullActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
namespace LeanFormal.IUT.XiFPaper.S2807SG3bScalarActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))

local instance s2807gbMeasurable : MeasurableSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := borel _
local instance s2807gbBorel : BorelSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := ⟨rfl⟩

/-- SG3b: once the packet identity `actualC3LogShellTensorLogVolume = packetLogVolume`
is supplied, the upper gap reduces to the scalar inequality
`-packetLogVolume ≤ CThetaPaper * paperQAbsLog`. No ABC input. -/
theorem S2807_upperGap_of_packetLogVolume_le
    (logQ dmod dFpd fFpd eStar etaPrm packetLogVolume : Real)
    (hpacket : actualC3LogShellTensorLogVolume (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) = packetLogVolume)
    (hscalar : -packetLogVolume ≤ CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog fiveLabel logQ) :
    S2717UpperGap R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D logQ dmod dFpd fFpd eStar etaPrm := by
  rw [S2807_upperGap_iff_neg_tensorLogVolume]
  rwa [hpacket]

#print axioms S2807_upperGap_of_packetLogVolume_le
end LeanFormal.IUT.XiFPaper.S2807SG3bScalarActual
end

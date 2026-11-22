import tmp.sheaf.xif.paper.S2807ThetaHullVolumeIdentityActual
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
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
namespace LeanFormal.IUT.XiFPaper.S2807SG3aActual

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

local instance s2807gaMeasurable : MeasurableSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := borel _
local instance s2807gaBorel : BorelSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := ⟨rfl⟩

/-- SG3a: the S2717 theta-hull log-volume is the negative of the actual C3
tensor log-shell packet log-volume. -/
theorem S2807_thetaHullVolume_eq_neg_tensorLogVolume :
    S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D =
      - actualC3LogShellTensorLogVolume (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) := by
  rw [S2807_thetaHullVolume_eq_haarRegion]
  rfl

/-- SG3 reduction: S2717UpperGap is exactly the negative tensor-log-volume scalar
inequality. -/
theorem S2807_upperGap_iff_neg_tensorLogVolume
    (logQ dmod dFpd fFpd eStar etaPrm : Real) :
    S2717UpperGap R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D logQ dmod dFpd fFpd eStar etaPrm ↔
      - actualC3LogShellTensorLogVolume (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) ≤
        CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm * paperQAbsLog fiveLabel logQ := by
  unfold S2717UpperGap
  rw [S2807_thetaHullVolume_eq_neg_tensorLogVolume]

#print axioms S2807_thetaHullVolume_eq_neg_tensorLogVolume
#print axioms S2807_upperGap_iff_neg_tensorLogVolume
end LeanFormal.IUT.XiFPaper.S2807SG3aActual
end
import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2725GlobalThetaHullActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
namespace LeanFormal.IUT.XiFPaper.S2807ThetaHullVolumeIdentityActual

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

local instance s2807Measurable : MeasurableSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := borel _
local instance s2807Borel : BorelSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := ⟨rfl⟩

/-- SG1 of S2807: the S2717 theta-hull log-volume is exactly the negative actual
Haar log-volume of the C3 log-shell tensor region (the actual theta hull equals
that region by `globalThetaHull_eq_imageSet`). -/
theorem S2807_thetaHullVolume_eq_haarRegion :
    S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D =
      - (haarLogVolume (actualC3LogShellTensorHaar (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D))
          (actualC3LogShellTensorRegion (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D))).toReal := by
  unfold S2717ThetaHullLogVolume
  simp only [globalThetaHullInterface, globalThetaLogVolume]
  rw [globalThetaHull_eq_imageSet]
  rfl

/-- SG1 consumer: the full paper 3.12 target is exactly the corresponding
three inequalities on the actual Haar log-volume of the C3 log-shell region. -/
theorem S2807_paperCor312Full_iff_haarRegion
    (v : FinitePrimePlace 2 7)
    (logQ dmod dFpd fFpd eStar etaPrm : Real) :
    PaperCor312Full R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat places tuple nu D v
        logQ dmod dFpd fFpd eStar etaPrm ↔
      S2717QPilotLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat
        ≤ - (haarLogVolume (actualC3LogShellTensorHaar
            (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
              horbCompat secCompat hsecCompat cusCompat hcusCompat D))
          (actualC3LogShellTensorRegion
            (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
              horbCompat secCompat hsecCompat cusCompat hcusCompat D))).toReal
        ∧
      - (haarLogVolume (actualC3LogShellTensorHaar
            (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
              horbCompat secCompat hsecCompat cusCompat hcusCompat D))
          (actualC3LogShellTensorRegion
            (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat
              horbCompat secCompat hsecCompat cusCompat hcusCompat D))).toReal
        ≤ S2715CThetaPaperScaleActual.CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm *
            S2691ExactQNormalizationActual.paperQAbsLog fiveLabel logQ
        ∧ -1 ≤ S2715CThetaPaperScaleActual.CThetaPaper fiveLabel logQ dmod dFpd fFpd eStar etaPrm := by
  rw [PaperCor312Full, S2717UpperGap, S2807_thetaHullVolume_eq_haarRegion]

#print axioms S2807_thetaHullVolume_eq_haarRegion
end LeanFormal.IUT.XiFPaper.S2807ThetaHullVolumeIdentityActual
end

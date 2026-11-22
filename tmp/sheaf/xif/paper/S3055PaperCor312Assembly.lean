import tmp.sheaf.xif.paper.S3053UpperGapClosed
import tmp.sheaf.xif.paper.PaperLevelXiFTargetBridgeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3053UpperGapClosed
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3055PaperCor312Assembly

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))

/-- Assembly: S3053 supplies the actual upper gap; the remaining four q-pilot
identification data are explicit inputs. -/
theorem S3055_paperCor312Full_of_q_bridge
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (v : FinitePrimePlace 2 7)
    (a b c : Nat) (habc : IsABCTriple a b c)
    (qParameter : Real)
    (hq : Real.log qParameter ≠ 0)
    (habs : |Real.log qParameter| = paperQAbsLog fiveLabel 1)
    (hqPilot :
      S2717QPilotLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat =
      -|Real.log qParameter|)
    (hxi :
      S2717QPilotLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat <=
      S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D) :
    PaperCor312Full R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D v
      1 0 S2990DFpd (S2990FFpd a b c) 0 0 := by
  exact S2717_full_of_hupper R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
    places tuple nu D v 1 0 S2990DFpd (S2990FFpd a b c) 0 0
    qParameter hq habs hqPilot hxi
    (S3053_upperGap R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat D
      places tuple nu a b c habc)

#check S3055_paperCor312Full_of_q_bridge

end LeanFormal.IUT.XiFPaper.S3055PaperCor312Assembly
end
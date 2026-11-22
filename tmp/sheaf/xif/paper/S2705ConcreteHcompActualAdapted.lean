import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.S2694GaussExponentSumClosedFormActual
import tmp.sheaf.xif.paper.ConcreteCor312ConclusionActualAdapted
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2705ConcreteHcompActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteCor312ConclusionActualAdapted
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S2694GaussExponentSumClosedFormActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open MeasureTheory

theorem S2705_concreteSourceComparison
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors
      (I := sourceHaarActualOriginalInput
        (S2696SourceData fiveLabel R redCompat hredCompat torCompat htorCompat
          orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)))
    (v : FinitePrimePlace 2 7) :
    concreteSourceComparison
      (concreteQPilotObject
        (I := sourceHaarActualOriginalInput
          (S2696SourceData fiveLabel R redCompat hredCompat torCompat htorCompat
            orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)))
      (unconditionalConcreteHull
        (I := sourceHaarActualOriginalInput
          (S2696SourceData fiveLabel R redCompat hredCompat torCompat htorCompat
            orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
        places tuple D nu) := by
  unfold concreteSourceComparison concreteQLogVolume
  rw [paperQPilotObjectConcrete_qPilotLogVolume]
  rw [sourceQPilotSignedLog]
  have havg :
      (unconditionalConcreteHull
        (I := sourceHaarActualOriginalInput
          (S2696SourceData fiveLabel R redCompat hredCompat torCompat htorCompat
            orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
        places tuple D nu).procession.average = 2 * Real.log 5 := by
    rw [unconditionalPaperSignedHull_procession_eq]
    exact S2694_signedAverage_five _ D
  rw [havg]
  have hgt := two_log5_lt_sourceBadQAbsLog fiveLabel R redCompat hredCompat
    torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
  linarith

#check S2705_concreteSourceComparison
#print axioms S2705_concreteSourceComparison
end LeanFormal.IUT.XiFPaper.S2705ConcreteHcompActualAdapted
end

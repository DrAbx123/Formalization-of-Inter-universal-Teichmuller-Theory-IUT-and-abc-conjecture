import tmp.sheaf.xif.paper.S2712MultiQConsumerActual
import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import tmp.sheaf.xif.paper.S2706DirectHcompActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataUnconditionalActual
import tmp.sheaf.xif.paper.ConcreteSignedHullUnconditionalActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2714MultiConcreteActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotIdentificationsActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2712MultiQConsumerActual
open LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open MeasureTheory
open scoped BigOperators

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]

local instance : Preorder (ConcreteFiniteTheorem311.ProcessionChoice fiveLabel) :=
  concreteProcessionChoicePreorder fiveLabel

noncomputable def S2714I
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    OriginalInput fiveLabel (FinitePrimePlace 2 7) :=
  S2706I (l := fiveLabel) R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat

noncomputable def S2714O
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    PaperQPilotObject (l := fiveLabel) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel fiveLabel)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice fiveLabel)
      (S2714I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat)
      (ConcreteKummerGroup (l := fiveLabel)) (concreteQPilotStrip (l := fiveLabel)) :=
  paperQPilotObject_multi
    (paperQPilotObjectConcrete (l := fiveLabel) (I := S2714I R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
    (MultiPlaceQPilotDonor.ofSource (I := S2714I R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))

noncomputable def S2714P
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (Ddon : SourcePilotRegionDonors (S2714I R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel fiveLabel.value) :=
  unconditionalHull (l := fiveLabel) (I := S2714I R redCompat hredCompat torCompat
    htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
    places tuple Ddon nu

theorem S2714P_average
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (Ddon : SourcePilotRegionDonors (S2714I R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    (S2714P places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon).procession.average
      = 2 * Real.log 5 := by
  rw [show (S2714P places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon).procession =
      c3ThetaSignedProcession (actualSignedC3 (l := fiveLabel)
        (V := FinitePrimePlace 2 7) (I := S2714I R redCompat hredCompat torCompat
          htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) Ddon) from
    unconditionalPaperSignedHull_procession_eq (l := fiveLabel) (I := S2714I R redCompat
      hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
      cusCompat hcusCompat) places tuple Ddon nu]
  exact signedAverage_eq_two_log5 (S2714I R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) Ddon

theorem S2714O_qPilotLogVolume
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume
      = -sourceBadQAbsLog (S2714I R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial := by
  unfold S2714O
  exact multiQPaperQPilotObject_qPilotLogVolume (I := S2714I R redCompat hredCompat
    torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
    (MultiPlaceQPilotDonor.ofSource)

theorem S2714_concrete_ineq
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (Ddon : SourcePilotRegionDonors (S2714I R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume
      ≤ (S2714P places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon).signedHullLogVolume := by
  have hbad : 2 * Real.log 5 ≤ sourceBadQAbsLog (S2714I R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat).initial :=
    le_of_lt (two_log5_lt_sourceBadQAbsLog (l := fiveLabel) R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
  rw [S2714O_qPilotLogVolume R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat]
  rw [show (S2714P places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon).signedHullLogVolume
      = -(S2714P places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon).procession.average from
    (S2714P places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon).signedHullLogVolume_eq_neg_average]
  rw [S2714P_average places tuple nu R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon]
  linarith

noncomputable def S2714J
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (Ddon : SourcePilotRegionDonors (S2714I R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    MultiQPaperXiFInclusion
      (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat)
      (S2714P places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon)
      (MultiPlaceQPilotDonor.ofSource (I := S2714I R redCompat hredCompat torCompat
        htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :=
  multiQPaperXiFInclusion _ _ _
    (paperQPilotIdentificationsActual (l := fiveLabel) (S2714I R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat)).paper_strip
    (paperQPilotIdentificationsActual (l := fiveLabel) (S2714I R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat)).paper_lineBundle
    (paperQPilotIdentificationsActual (l := fiveLabel) (S2714I R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat)).paper_logKummer
    (paperQPilotIdentificationsActual (l := fiveLabel) (S2714I R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat)).paper_qPilot_log
    (S2714_concrete_ineq places tuple nu R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon)

theorem qPilot_le_signedHull_multi
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (Ddon : SourcePilotRegionDonors (S2714I R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume
      ≤ (S2714P places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon).signedHullLogVolume :=
  MultiQPaperXiFInclusion.qPilot_le_signedHull
    (S2714J places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon)

theorem qPilot_mem_ray_multi
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (Ddon : SourcePilotRegionDonors (S2714I R redCompat hredCompat torCompat
      htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).qPilotLogVolume
      ∈ hullLogVolumeRay (S2714P places tuple nu R redCompat hredCompat torCompat
        htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
        Ddon).signedHullLogVolume :=
  MultiQPaperXiFInclusion.qPilot_mem_ray
    (S2714J places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon)

#print axioms qPilot_le_signedHull_multi
#print axioms qPilot_mem_ray_multi

end LeanFormal.IUT.XiFPaper.S2714MultiConcreteActualAdapted
end

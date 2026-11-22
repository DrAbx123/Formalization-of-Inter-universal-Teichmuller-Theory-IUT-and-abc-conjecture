import tmp.sheaf.xif.paper.S2712MultiQConsumerActual
import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import tmp.sheaf.xif.paper.S2706DirectHcompActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.ConcreteSignedHullUnconditionalActual
import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataUnconditionalActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2714SecondActualAdapted

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
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
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
variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)

noncomputable def S2714I : OriginalInput fiveLabel (FinitePrimePlace 2 7) :=
  S2706I R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat

variable (Ddon : SourcePilotRegionDonors S2714I)

noncomputable def S2714Q : MultiPlaceQPilotDonor S2714I :=
  MultiPlaceQPilotDonor.ofSource

noncomputable def S2714O : PaperQPilotObject (l := fiveLabel)
    (V := FinitePrimePlace 2 7)
    (Label := ConcreteFiniteTheorem311.finiteLabel fiveLabel)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice fiveLabel)
    S2714I (ConcreteKummerGroup (l := fiveLabel)) (concreteQPilotStrip (l := fiveLabel)) :=
  paperQPilotObject_multi (paperQPilotObjectConcrete (l := fiveLabel) (I := S2714I)) S2714Q

noncomputable def S2714P : PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel fiveLabel) :=
  unconditionalHull (l := fiveLabel) (I := S2714I) places tuple Ddon nu

theorem S2714P_average :
    (S2714P places tuple Ddon nu).procession.average = 2 * Real.log 5 := by
  rw [show (S2714P places tuple Ddon nu).procession =
      c3ThetaSignedProcession (actualSignedC3 (l := fiveLabel)
        (V := FinitePrimePlace 2 7) (I := S2714I) Ddon) from
    unconditionalPaperSignedHull_procession_eq (l := fiveLabel) (I := S2714I)
      places tuple Ddon nu]
  exact signedAverage_eq_two_log5 S2714I Ddon

theorem S2714O_qPilotLogVolume :
    (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat Ddon).qPilotLogVolume
      = -sourceBadQAbsLog S2714I.initial := by
  rw [show S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat Ddon
      = paperQPilotObject_multi (paperQPilotObjectConcrete (l := fiveLabel) (I := S2714I)) S2714Q from rfl]
  rw [paperQPilotObject_multi_qPilotLogVolume, paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog]

theorem S2714I_hqMulti :
    sourceQPilotSignedLog S2714I.initial = paperQPilotLogVolume_multi S2714Q :=
  hqMulti_holds S2714Q

theorem S2714_concrete_ineq :
    (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat Ddon).qPilotLogVolume
      ≤ (S2714P places tuple Ddon nu).signedHullLogVolume := by
  have hdirect := S2706_directHcomp (l := fiveLabel) R redCompat hredCompat
    torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
    (P := S2714P places tuple Ddon nu) (S2714P_average places tuple Ddon nu)
  have hvol :
      (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat Ddon).qPilotLogVolume =
        (paperQPilotObjectConcrete (l := fiveLabel) (I := S2714I
          R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
          secCompat hsecCompat cusCompat hcusCompat)).qPilotLogVolume := by
    rw [show S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat Ddon =
          paperQPilotObject_multi
            (paperQPilotObjectConcrete (l := fiveLabel) (I := S2714I
              R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
              secCompat hsecCompat cusCompat hcusCompat)) S2714Q from rfl]
    rw [paperQPilotObject_multi_qPilotLogVolume,
      paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog]
    unfold sourceQPilotSignedLog
    exact (S2706_O_qPilotLogVolume (l := fiveLabel) R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat
      hcusCompat).symm
  rw [hvol]
  simpa [concreteSourceComparison] using hdirect

noncomputable def S2714J :
    MultiQPaperXiFInclusion
      (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat Ddon)
      (S2714P places tuple Ddon nu) S2714Q :=
  multiQPaperXiFInclusion _ _ _
    (paperQPilotIdentificationsActual (l := fiveLabel) S2714I).paper_strip
    (paperQPilotIdentificationsActual (l := fiveLabel) S2714I).paper_lineBundle
    (paperQPilotIdentificationsActual (l := fiveLabel) S2714I).paper_logKummer
    (paperQPilotIdentificationsActual (l := fiveLabel) S2714I).paper_qPilot_log
    (S2714_concrete_ineq places tuple nu R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon)

theorem S2714_qPilot_le_signedHull_multi :
    (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat Ddon).qPilotLogVolume
      ≤ (S2714P places tuple Ddon nu).signedHullLogVolume :=
  MultiQPaperXiFInclusion.qPilot_le_signedHull
    (S2714J places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon)

theorem S2714_qPilot_mem_ray_multi :
    (S2714O R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat Ddon).qPilotLogVolume
      ∈ hullLogVolumeRay (S2714P places tuple Ddon nu).signedHullLogVolume :=
  MultiQPaperXiFInclusion.qPilot_mem_ray
    (S2714J places tuple nu R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat Ddon)

#print axioms S2714_qPilot_le_signedHull_multi
#print axioms S2714_qPilot_mem_ray_multi
#print axioms S2714I_hqMulti

end LeanFormal.IUT.XiFPaper.S2714SecondActualAdapted
end

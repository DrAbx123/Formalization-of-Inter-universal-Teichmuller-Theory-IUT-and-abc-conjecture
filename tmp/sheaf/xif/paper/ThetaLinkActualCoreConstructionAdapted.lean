import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual
import tmp.sheaf.xif.paper.PaperSignedHullActualAdapted
import tmp.sheaf.xif.paper.ConcreteQPilotLogIdentificationActual
import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.n8.closure.C3Actual

-- Core ThetaLinkActual construction from actual O/P/C3 data.
--
-- O := paperQPilotObjectConcrete I (actual PaperQPilotObject).
-- C3 := sourcePilotRegionDataOfDonors D (actual source C3, donor q, not q=1/5).
-- P := paperSignedHullFromTheater C3 with exact haverage/hnormal inputs.
-- qPilotLogVolume_eq_paper from the exact source-q identification hq.
-- link_identification := concreteSourceComparison O P;
-- link_implies_inclusion := actual concreteMembership_of_sourceComparison.
-- No q=1/5 concrete C3 path and no value-layer substitution.
-- WRITE-ONLY; local compile after write.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.ThetaLinkActualCoreConstructionAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperSignedHullActualAdapted
open LeanFormal.IUT.XiFPaper.ConcreteQPilotLogIdentificationActual
open MeasureTheory
open scoped BigOperators

universe uK uW

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]
variable (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
variable (hbad : Nonempty I.initial.badPlaces)

noncomputable def thetaLinkC3 :
    SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I :=
  sourcePilotRegionDataOfDonors (l := l) (V := FinitePrimePlace 2 7) (I := I) D

noncomputable def thetaLinkO :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (ConcreteKummerGroup (l := l)) (concreteQPilotStrip (l := l)) :=
  concreteQPilotObject (l := l) (I := I)

noncomputable def thetaLinkP
    (haverage : 0 <= (c3ThetaProcession (thetaLinkC3 (l := l) (I := I) D)).average)
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal
          (c3ThetaProcession (thetaLinkC3 (l := l) (I := I) D)).average) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  paperSignedHullFromTheater (I := I) places tuple mu
    (thetaLinkC3 (l := l) (I := I) D) haverage hnormal

theorem thetaLinkO_qPilotLogVolume_eq_paper
    (hq : ConcreteSourceQIdentification (l := l) (I := I)
      (thetaLinkC3 (l := l) (I := I) D)) :
    (thetaLinkO (l := l) (I := I)).qPilotLogVolume =
      paperQPilotLogVolume (thetaLinkC3 (l := l) (I := I) D) :=
  concreteO_qPilotLogVolume_eq_paper
    (thetaLinkO (l := l) (I := I))
    (thetaLinkC3 (l := l) (I := I) D) hq

theorem thetaLinkO_qPilotLogVolume_neg
    (hbad : Nonempty I.initial.badPlaces) :
    (thetaLinkO (l := l) (I := I)).qPilotLogVolume < 0 := by
  rw [(thetaLinkO (l := l) (I := I)).qPilotLogVolume_eq]
  exact sourceQPilotSignedLog_neg_of_nonempty I.initial hbad

theorem thetaLinkO_qPilotLogVolume_ne_zero
    (hbad : Nonempty I.initial.badPlaces) :
    (thetaLinkO (l := l) (I := I)).qPilotLogVolume ≠ 0 :=
  ne_of_lt (thetaLinkO_qPilotLogVolume_neg (l := l) (I := I) hbad)

noncomputable def thetaLinkActual
    (hq : ConcreteSourceQIdentification (l := l) (I := I)
      (thetaLinkC3 (l := l) (I := I) D))
    (haverage : 0 <= (c3ThetaProcession (thetaLinkC3 (l := l) (I := I) D)).average)
    (hnormal :
      (C6ActualIQData.actual places tuple mu).iqInterface.logVolume
          (C6ActualIQData.actual places tuple mu).hull =
        ENNReal.ofReal
          (c3ThetaProcession (thetaLinkC3 (l := l) (I := I) D)).average)
    (hbad : Nonempty I.initial.badPlaces) :
    ThetaLinkActual (thetaLinkO (l := l) (I := I))
      (thetaLinkP (l := l) (I := I) places tuple mu D haverage hnormal)
      (thetaLinkC3 (l := l) (I := I) D) where
  qPilot_identifications := by
    unfold thetaLinkQPilotPaperIdentifications
    exact ⟨
      (paperQPilotIdentificationsActual (l := l) I).paper_strip,
      (paperQPilotIdentificationsActual (l := l) I).paper_lineBundle,
      (paperQPilotIdentificationsActual (l := l) I).paper_logKummer,
      (paperQPilotIdentificationsActual (l := l) I).paper_qPilot_log⟩
  qPilotLogVolume_eq_paper :=
    thetaLinkO_qPilotLogVolume_eq_paper (l := l) (I := I) D hq
  qParameter := Real.exp (thetaLinkO (l := l) (I := I)).qPilotLogVolume
  qParameter_pos := Real.exp_pos _
  qParameter_log_ne_zero := by
    rw [Real.log_exp]
    exact thetaLinkO_qPilotLogVolume_ne_zero (l := l) (I := I) hbad
  qPilotLogVolume_eq_neg_abs := by
    rw [Real.log_exp]
    have hneg := thetaLinkO_qPilotLogVolume_neg (l := l) (I := I) hbad
    rw [abs_of_neg hneg]
    ring
  link_identification :=
    concreteSourceComparison (thetaLinkO (l := l) (I := I))
      (thetaLinkP (l := l) (I := I) places tuple mu D haverage hnormal)
  link_implies_inclusion :=
    concreteMembership_of_sourceComparison
      (thetaLinkO (l := l) (I := I))
      (thetaLinkP (l := l) (I := I) places tuple mu D haverage hnormal)

#check thetaLinkActual

end LeanFormal.IUT.XiFPaper.ThetaLinkActualCoreConstructionAdapted

end
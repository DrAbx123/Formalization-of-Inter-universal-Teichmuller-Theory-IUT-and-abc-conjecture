import tmp.sheaf.xif.paper.ConcreteSignedHullUnconditionalActual
import tmp.sheaf.xif.paper.ConcreteQPilotLogIdentificationActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual
import tmp.sheaf.xif.paper.ThetaLinkActual

-- Actual ThetaLinkActual construction from concrete q-pilot, unconditional
-- signed hull, and the actual source comparison.
--
-- O := concreteQPilotObject (actual PaperQPilotObject)
-- P := unconditionalHull (actual normalized-Haar PaperSignedHull)
-- C3 := actualSignedC3 D (actual source-theater C3)
-- link_identification := concreteSourceComparison O P
-- link_implies_inclusion := actual concreteMembership_of_sourceComparison.
-- The q-pilot paper scalar equality is the exact input hq
-- (ConcreteSourceQIdentification); it is not fabricated.
-- WRITE-ONLY; local compile after write.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.ThetaLinkActualConstructionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper.PaperQPilotIdentificationsActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteQPilotLogIdentificationActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open MeasureTheory
open scoped BigOperators

universe ua upi umon ui uK uW

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
variable (v : FinitePrimePlace 2 7)
variable (hbad : Nonempty I.initial.badPlaces)

noncomputable def thetaLinkO :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (ConcreteKummerGroup (l := l)) (concreteQPilotStrip (l := l)) :=
  concreteQPilotObject (l := l) (I := I)

noncomputable def thetaLinkP :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  unconditionalPaperSignedHull (l := l) (V := FinitePrimePlace 2 7)
    (I := I) places tuple D nu

noncomputable def thetaLinkC3 :
    SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I :=
  actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D

theorem thetaLinkO_qPilotLogVolume_eq_paper
    (hq : ConcreteSourceQIdentification (l := l) (I := I)
      (thetaLinkC3 (l := l) (I := I) D)) :
    (thetaLinkO (l := l) (I := I)).qPilotLogVolume =
      paperQPilotLogVolume
        (thetaLinkC3 (l := l) (I := I) D) :=
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
    (thetaLinkO (l := l) (I := I)).qPilotLogVolume ≠ 0 := by
  exact ne_of_lt (thetaLinkO_qPilotLogVolume_neg (l := l) (I := I) hbad)

-- Actual ThetaLinkActual, conditional only on the exact q-paper scalar
-- identification hq. The link implication is the actual concrete membership
-- proof, not a value-layer inequality.
noncomputable def thetaLinkActual
    (hq : ConcreteSourceQIdentification (l := l) (I := I)
      (thetaLinkC3 (l := l) (I := I) D))
    (hbad : Nonempty I.initial.badPlaces) :
    ThetaLinkActual (thetaLinkO (l := l) (I := I))
      (thetaLinkP (l := l) (I := I) places tuple D nu)
      (thetaLinkC3 (l := l) (I := I) D) where
  qPilot_identifications := by
    unfold thetaLinkQPilotPaperIdentifications
    exact ⟨
      (paperQPilotIdentificationsActual (l := l) I).paper_strip,
      (paperQPilotIdentificationsActual (l := l) I).paper_lineBundle,
      (paperQPilotIdentificationsActual (l := l) I).paper_logKummer,
      (paperQPilotIdentificationsActual (l := l) I).paper_qPilot_log⟩
  qPilotLogVolume_eq_paper :=
    thetaLinkO_qPilotLogVolume_eq_paper (l := l) (I := I) places tuple D hq
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
      (thetaLinkP (l := l) (I := I) places tuple D nu)
  link_implies_inclusion :=
    concreteMembership_of_sourceComparison
      (thetaLinkO (l := l) (I := I))
      (thetaLinkP (l := l) (I := I) places tuple D nu)

#check thetaLinkActual

end LeanFormal.IUT.XiFPaper.ThetaLinkActualConstructionActualAdapted

end
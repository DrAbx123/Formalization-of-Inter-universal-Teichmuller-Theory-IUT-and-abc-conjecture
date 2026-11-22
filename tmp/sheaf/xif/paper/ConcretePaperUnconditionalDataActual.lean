import tmp.sheaf.xif.paper.ConcretePaperQPilotWitnessActual
import tmp.sheaf.xif.paper.ConcretePaperSignedHullActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual
import tmp.sheaf.xif.paper.PaperXiFUnconditional
import tmp.sheaf.xif.paper.IPLAPTDataActual
import tmp.sheaf.n8.closure.C3Actual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

-- Actual concrete PaperUnconditionalData skeleton
--
-- Packages the actual concrete q-pilot witness, the actual concrete signed
-- PaperSignedHull, and the actual self IPL/Kummer-evaluation Theta-link data.
-- The still-missing hnormal equality, q-pilot log normalization equality, and
-- source comparison are exact inputs (ConcreteHnormalEquality / actual
-- equalities / concreteSourceComparison); no True, empty type, PUnit or toy.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotIdentificationsActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.XiFPaper.ConcretePaperQPilotWitnessActual
open LeanFormal.IUT.XiFPaper.ConcretePaperSignedHullActual
open LeanFormal.IUT.XiFPaper.ConcreteHnormalActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Actual
open MeasureTheory
open scoped BigOperators

universe ua upi umon ui uK uW

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]
variable (D : SourcePilotRegionDonors I)
variable (v : FinitePrimePlace 2 7)

-- The actual concrete q-pilot object.
abbrev concreteQPilotObject :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (ConcreteKummerGroup (l := l)) (concreteQPilotStrip (l := l)) :=
  paperQPilotObjectConcrete (l := l) I

-- The actual concrete signed hull.
abbrev concreteHull
    (h : ConcreteHnormalEquality (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D) :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  concretePaperSignedHull (l := l) (V := FinitePrimePlace 2 7) (I := I)
    places tuple mu D h

-- The actual self IPL/Kummer-evaluation Theta-link on the concrete q-pilot strip.
noncomputable def concreteThetaLinkData :
    PaperThetaLinkData (G := ConcreteKummerGroup (l := l))
      (intermediateStrip := concreteQPilotStrip (l := l))
      (gauStrip := concreteQPilotStrip (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (coricEnvStrip := concreteQPilotStrip (l := l))
      (qPilotStrip := concreteQPilotStrip (l := l))
      (upperLeft := concreteQPilotStrip (l := l))
      (upperRight := concreteQPilotStrip (l := l))
      (lowerLeft := concreteQPilotStrip (l := l))
      (lowerRight := concreteQPilotStrip (l := l)) where
  ipl := selfIplActual (concreteQPilotStrip (l := l))
  kummerEvaluation := selfKummerEvaluationActual (concreteQPilotStrip (l := l))

-- Actual skeleton of PaperUnconditionalData, with exact input hypotheses for
-- hnormal, q-pilot log normalization, and the source comparison.
noncomputable def concretePaperUnconditionalData
    (hnormal : ConcreteHnormalEquality (l := l) (V := FinitePrimePlace 2 7) (I := I)
      places tuple mu D)
    (hq : (concreteQPilotObject (l := l) (I := I)).qPilotLogVolume =
      paperQPilotLogVolume (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D))
    (hcomp : concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
      (concreteHull (l := l) (I := I) places tuple mu D hnormal)) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (concreteQPilotObject (l := l) (I := I))
      (concreteHull (l := l) (I := I) places tuple mu D hnormal)
      (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) where
  sourceLink := {
    source_identifications := ⟨
      (paperQPilotIdentificationsActual (l := l) I).paper_strip,
      (paperQPilotIdentificationsActual (l := l) I).paper_lineBundle,
      (paperQPilotIdentificationsActual (l := l) I).paper_logKummer,
      (paperQPilotIdentificationsActual (l := l) I).paper_qPilot_log⟩,
    qPilotLogVolume_eq_paper := hq,
    link_identification :=
      concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
        (concreteHull (l := l) (I := I) places tuple mu D hnormal),
    link_implies_inclusion :=
      concreteMembership_of_sourceComparison
        (concreteQPilotObject (l := l) (I := I))
        (concreteHull (l := l) (I := I) places tuple mu D hnormal) }
  sourceLink_holds := hcomp
  thetaLink := concreteThetaLinkData (l := l)

#check concreteQPilotObject
#check concreteHull
#check concreteThetaLinkData
#check concretePaperUnconditionalData

end LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual

end
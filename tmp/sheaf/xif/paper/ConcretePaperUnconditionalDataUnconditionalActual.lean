import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataActual
import tmp.sheaf.xif.paper.ConcreteSignedHullUnconditionalActual
import tmp.sheaf.xif.paper.ConcreteQPilotLogIdentificationActual
import tmp.sheaf.n8.closure.C3Actual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

-- Unconditional concrete PaperUnconditionalData
--
-- Removes the hnormal input by using the paper-normalized Haar measure
-- normalizedHaarMeasure nu and the proved concrete normalized hnormal
-- equality. The q-log equality is consumed from the actual qside q-log
-- identification (ConcreteSourceQIdentification); the source comparison is
-- kept as the exact input hcomp. No True/empty type/PUnit/toy.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataUnconditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotIdentificationsActual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.Theorem311Source.ConcreteQPilotLogIdentificationActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
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
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (D : SourcePilotRegionDonors I)
variable (v : FinitePrimePlace 2 7)

-- The unconditional concrete signed hull: no hnormal input, normalized Haar
-- measure only.
abbrev unconditionalHull :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  unconditionalPaperSignedHull (l := l) (V := FinitePrimePlace 2 7) (I := I)
    places tuple D nu

-- The actual qside q-log source identification used for hq.
abbrev concreteQLogIdentification : Prop :=
  ConcreteSourceQIdentification (I := I)
    (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D)

-- Actual q-log equality from the qside identification.
theorem concreteQPilotLogVolume_eq_paper
    (hq : concreteQLogIdentification (l := l) (I := I) D) :
    (concreteQPilotObject (l := l) (I := I)).qPilotLogVolume =
      paperQPilotLogVolume
        (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) :=
  concreteO_qPilotLogVolume_eq_paper
    (concreteQPilotObject (l := l) (I := I))
    (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) hq

-- The unconditional PaperUnconditionalData skeleton: normalized Haar removes
-- hnormal; qside q-log identification supplies hq; source comparison remains
-- the exact input hcomp.
noncomputable def concretePaperUnconditionalDataUnconditional
    (hq : concreteQLogIdentification (l := l) (I := I) D)
    (hcomp : concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
      (unconditionalHull places tuple nu D)) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (concreteQPilotObject (l := l) (I := I))
      (unconditionalHull places tuple nu D)
      (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) where
  sourceLink := {
    source_identifications := ⟨
      (paperQPilotIdentificationsActual (l := l) I).paper_strip,
      (paperQPilotIdentificationsActual (l := l) I).paper_lineBundle,
      (paperQPilotIdentificationsActual (l := l) I).paper_logKummer,
      (paperQPilotIdentificationsActual (l := l) I).paper_qPilot_log⟩,
    qPilotLogVolume_eq_paper :=
      concreteQPilotLogVolume_eq_paper (l := l) (I := I) D hq,
    link_identification :=
      concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
        (unconditionalHull places tuple nu D),
    link_implies_inclusion :=
      concreteMembership_of_sourceComparison
        (concreteQPilotObject (l := l) (I := I))
        (unconditionalHull places tuple nu D) }
  sourceLink_holds := hcomp
  thetaLink := concreteThetaLinkData (l := l)

#check unconditionalHull
#check concreteQLogIdentification
#check concreteQPilotLogVolume_eq_paper
#check concretePaperUnconditionalDataUnconditional

end LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataUnconditionalActual

end
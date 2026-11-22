import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataActual
import tmp.sheaf.xif.paper.ConcreteSignedHullUnconditionalActual
import tmp.sheaf.xif.paper.NormalizedHaarHnormalActual

/-!
# Concrete Cor312 / PaperXiFInclusion skeleton with the unconditional hull

This file plugs the unconditional concrete signed hull (built from the
paper-normalized Haar measure) into the concrete PaperUnconditionalData
skeleton.  The hnormal equality is no longer an input: it is the proved
`normalizedHaarMeasure_concreteHnormalEquality`.

Two source comparison propositions remain explicit exact obstacles:

* `ConcreteQPilotLogNormalizationObstacle`: the concrete q-pilot scalar equals
  `paperQPilotLogVolume (actualSignedC3 D)`;
* `UnconditionalSourceComparisonObstacle`: the signed-hull procession average
  is bounded by the negative concrete q-pilot scalar.

They are not asserted.  Under them the actual `PaperXiFInclusion` skeleton and
the actual Cor312 consumer are assembled.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace ConcreteCor312ConclusionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper.PaperQPilotIdentificationsActual
open LeanFormal.IUT.XiFPaper.ConcretePaperQPilotWitnessActual
open LeanFormal.IUT.XiFPaper.ConcretePaperSignedHullActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.ConcreteHnormalActual
open LeanFormal.IUT.XiFPaper.NormalizedHaarHnormalActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open MeasureTheory
open scoped BigOperators

universe ua upi umon ui uK uW

variable {l : PrimeGeFive}
variable {I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
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

/-- The unconditional concrete signed hull: the normalized Haar measure is
used instead of an assumed hnormal. -/
abbrev unconditionalConcreteHull :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  unconditionalPaperSignedHull (l := l) (V := FinitePrimePlace 2 7)
    (I := I) places tuple D nu

/-- Exact q-pilot log normalization obstacle. -/
def ConcreteQPilotLogNormalizationObstacle : Prop :=
  (concreteQPilotObject (l := l) (I := I)).qPilotLogVolume =
    paperQPilotLogVolume
      (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D)

/-- Exact source comparison obstacle for the unconditional concrete hull. -/
def UnconditionalSourceComparisonObstacle : Prop :=
  concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
    (unconditionalConcreteHull (l := l) (I := I) places tuple D nu)

/-- The concrete PaperUnconditionalData with hnormal discharged by the
normalized Haar measure; only the two exact source comparison propositions are
inputs. -/
noncomputable def unconditionalPaperUnconditionalData
    (hq : ConcreteQPilotLogNormalizationObstacle (l := l) (I := I) D)
    (hcomp : UnconditionalSourceComparisonObstacle (l := l) (I := I)
      places tuple D nu) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (concreteQPilotObject (l := l) (I := I))
      (unconditionalConcreteHull (l := l) (I := I) places tuple D nu)
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
        (unconditionalConcreteHull (l := l) (I := I) places tuple D nu),
    link_implies_inclusion :=
      concreteMembership_of_sourceComparison
        (concreteQPilotObject (l := l) (I := I))
        (unconditionalConcreteHull (l := l) (I := I) places tuple D nu) }
  sourceLink_holds := hcomp
  thetaLink := concreteThetaLinkData (l := l)

/-- The actual PaperXiFInclusion assembled from the unconditional hull and the
two exact source comparison propositions. -/
noncomputable def unconditionalPaperXiFInclusion
    (hq : ConcreteQPilotLogNormalizationObstacle (l := l) (I := I) D)
    (hcomp : UnconditionalSourceComparisonObstacle (l := l) (I := I)
      places tuple D nu) :
    PaperXiFInclusion
      (concreteQPilotObject (l := l) (I := I))
      (unconditionalConcreteHull (l := l) (I := I) places tuple D nu)
      (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D) :=
  ⟨(unconditionalPaperUnconditionalData (l := l) (I := I)
      places tuple D nu v hq hcomp).sourceLink,
    (unconditionalPaperUnconditionalData (l := l) (I := I)
      places tuple D nu v hq hcomp).sourceLink_holds⟩

/-- The actual q-pilot ray membership from the unconditional hull and the exact
source comparison. -/
theorem unconditional_qPilot_mem_ray
    (hq : ConcreteQPilotLogNormalizationObstacle (l := l) (I := I) D)
    (hcomp : UnconditionalSourceComparisonObstacle (l := l) (I := I)
      places tuple D nu) :
    (concreteQPilotObject (l := l) (I := I)).qPilotLogVolume ∈
      hullLogVolumeRay
        (unconditionalConcreteHull (l := l) (I := I) places tuple D nu).signedHullLogVolume :=
  (unconditionalPaperXiFInclusion (l := l) (I := I)
    places tuple D nu v hq hcomp).qPilot_mem_ray

end ConcreteCor312ConclusionActualAdapted
end LeanFormal.IUT.XiFPaper
end

import tmp.sheaf.xif.paper.ConcreteSourceComparisonActual
import tmp.sheaf.xif.paper.ConcreteSignedHullUnconditionalActual
import tmp.sheaf.xif.paper.ConcretePaperQPilotWitnessActual
import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataActual
import tmp.sheaf.xif.paper.PaperQPilotIdentificationsActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.PaperQPilotLogVolume

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Concrete PaperXiFInclusion / PaperUnconditionalData from the concrete link

This file constructs the actual inclusion/data layer from:

* the concrete q-pilot witness / object paperQPilotObjectConcrete;
* unconditionalPaperSignedHull, the actual concrete signed hull built from the
  normalized Haar measure;
* concreteSourceLink, whose link_identification is the exact concrete
  comparison and whose link_implies_inclusion is the actual signed-hull ray
  membership.

The link identification is never True: it is the concrete comparison
P.procession.average <= -O.qPilotLogVolume. The inclusion holds only under that
explicit comparison proof. The remaining q-pilot log normalization equality is
an explicit input, not fabricated.

No True/PUnit, empty type, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ConcretePaperXiFInclusionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper.ConcretePaperQPilotWitnessActual
open LeanFormal.IUT.XiFPaper.ConcretePaperSignedHullActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonActual
open LeanFormal.IUT.XiFPaper.PaperQPilotIdentificationsActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual
open LeanFormal.IUT.N8C6ActualIQ
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

/-- The concrete q-pilot object. -/
abbrev concreteQPilotObject :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (ConcreteKummerGroup (l := l)) (concreteQPilotStrip (l := l)) :=
  paperQPilotObjectConcrete (l := l) I

/-- The actual unconditional concrete signed hull. -/
noncomputable abbrev concreteUnconditionalHull :
    PaperSignedHull (PaperC6Carrier places tuple) (SignedLabel l.value) :=
  unconditionalPaperSignedHull (l := l) (V := FinitePrimePlace 2 7) (I := I)
    places tuple D nu

/-- The actual source-theater C3. -/
noncomputable abbrev concreteC3 :
    SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I :=
  actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D

/-- The concrete source link, with the exact comparison as identification. -/
noncomputable def concretePaperXiFSourceLink
    (hq : (concreteQPilotObject (l := l) I).qPilotLogVolume =
      paperQPilotLogVolume (concreteC3 (l := l) (I := I) D)) :
    PaperXiFSourceLink (concreteQPilotObject (l := l) I)
      (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)
      (concreteC3 (l := l) (I := I) D) where
  source_identifications := ⟨
    (paperQPilotIdentificationsActual (l := l) I).paper_strip,
    (paperQPilotIdentificationsActual (l := l) I).paper_lineBundle,
    (paperQPilotIdentificationsActual (l := l) I).paper_logKummer,
    (paperQPilotIdentificationsActual (l := l) I).paper_qPilot_log⟩
  qPilotLogVolume_eq_paper := hq
  link_identification :=
    (concreteSourceLink (l := l) I
      (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)).link_identification
  link_implies_inclusion := by
    intro h
    have hqlink :
        (concreteSourceLink (l := l) I
          (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)).qLogVolume =
          (concreteQPilotObject (l := l) I).qPilotLogVolume := by
      rw [(concreteSourceLink (l := l) I
        (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)).qLogVolume_eq]
      rfl
    have hmem := (concreteSourceLink (l := l) I
      (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)).link_implies_inclusion h
    rw [hqlink] at hmem
    exact hmem

/-- The concrete link identification is the exact concrete comparison. -/
theorem concretePaperXiFSourceLink_identification
    (hq : (concreteQPilotObject (l := l) I).qPilotLogVolume =
      paperQPilotLogVolume (concreteC3 (l := l) (I := I) D)) :
    (concretePaperXiFSourceLink (l := l) I places tuple D nu hq).link_identification =
      concreteSourceComparison (l := l) I
        (concreteUnconditionalHull (l := l) (I := I) places tuple D nu) :=
  rfl

/-- Concrete PaperXiFInclusion from an explicit comparison proof. -/
noncomputable def concretePaperXiFInclusion
    (hq : (concreteQPilotObject (l := l) I).qPilotLogVolume =
      paperQPilotLogVolume (concreteC3 (l := l) (I := I) D))
    (hcomp :
      (concreteSourceLink (l := l) I
        (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)).link_identification) :
    PaperXiFInclusion (concreteQPilotObject (l := l) I)
      (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)
      (concreteC3 (l := l) (I := I) D) where
  link := concretePaperXiFSourceLink (l := l) I places tuple D nu hq
  link_holds := hcomp

/-- Concrete paper xi-f membership from the explicit comparison. -/
theorem concretePaperXiF_membership
    (hq : (concreteQPilotObject (l := l) I).qPilotLogVolume =
      paperQPilotLogVolume (concreteC3 (l := l) (I := I) D))
    (hcomp :
      (concreteSourceLink (l := l) I
        (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)).link_identification) :
    (concreteQPilotObject (l := l) I).qPilotLogVolume ∈
      hullLogVolumeRay
        (concreteUnconditionalHull (l := l) (I := I) places tuple D nu).signedHullLogVolume :=
  (concretePaperXiFInclusion (l := l) I places tuple D nu hq hcomp).qPilot_mem_ray

/-- Concrete PaperUnconditionalData from the actual concrete source link and
the actual self IPL/Kummer-evaluation Theta-link. -/
noncomputable def concretePaperUnconditionalData
    (hq : (concreteQPilotObject (l := l) I).qPilotLogVolume =
      paperQPilotLogVolume (concreteC3 (l := l) (I := I) D))
    (hcomp :
      (concreteSourceLink (l := l) I
        (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)).link_identification) :
    PaperUnconditionalData (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      (I := I) (G := ConcreteKummerGroup (l := l))
      (envStrip := concreteQPilotStrip (l := l))
      (X := PaperC6Carrier places tuple)
      (label := SignedLabel l.value) v
      (concreteQPilotObject (l := l) I)
      (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)
      (concreteC3 (l := l) (I := I) D) where
  sourceLink := concretePaperXiFSourceLink (l := l) I places tuple D nu hq
  sourceLink_holds := hcomp
  thetaLink := ConcretePaperUnconditionalDataActual.concreteThetaLinkData (l := l) (I := I)

end LeanFormal.IUT.XiFPaper.ConcretePaperXiFInclusionActualAdapted

end

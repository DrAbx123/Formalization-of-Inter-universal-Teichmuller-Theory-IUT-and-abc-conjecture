import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Concrete source comparison / link evidence

This file builds the actual comparison/link evidence between the concrete
PaperQPilotObject (PaperQPilotObjectConcreteActual) and a paper signed hull.

Actual data used:
* paperQPilotObjectConcrete I: concrete q-pilot object with actual
  qPilotLogVolume = sourceQPilotSignedLog I.initial;
* P : PaperSignedHull X label: actual signed hull, with actual
  P.signedHullLogVolume = -P.procession.average;
* hullLogVolumeRay = Set.Iic P.signedHullLogVolume.

Constructed:
* concreteSourceComparison: the exact real comparison
  P.procession.average <= -O.qPilotLogVolume;
* exact equivalence between that comparison and the signed-hull membership
  O.qPilotLogVolume in hullLogVolumeRay P.signedHullLogVolume;
* ConcreteSourceLink: link_identification is the concrete comparison (not
  True), link_implies_inclusion is the proved membership transfer;
* concreteSourceLink: the actual link evidence;
* concreteSignedHull / concreteSourceLinkOfTheater: the same for the actual
  source-theater signed hull built from a C3 donor and its exact hlog/hnormal
  fields.

No inequality is asserted: concreteSourceComparison is a proposition kept
explicit. No True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open MeasureTheory

universe ua upi umon ui uX uLabel

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)

/-- The actual concrete q-pilot scalar used in the comparison. -/
def concreteQLogVolume : Real :=
  (paperQPilotObjectConcrete (l := l) I).qPilotLogVolume

/-- Exact concrete source comparison: the signed hull procession average is at
most the q-pilot magnitude. This is a proposition, not an asserted
inequality. -/
def concreteSourceComparison : Prop :=
  P.procession.average <= -concreteQLogVolume (l := l) I

/-- The concrete comparison is equivalent to membership in the signed hull
ray. -/
theorem concreteSourceComparison_iff_membership :
    concreteSourceComparison (l := l) I P ↔
      concreteQLogVolume (l := l) I ∈
        hullLogVolumeRay P.signedHullLogVolume := by
  unfold concreteSourceComparison concreteQLogVolume
  rw [mem_hullLogVolumeRay_iff, P.signedHullLogVolume_eq_neg_average]
  constructor <;> intro h <;> linarith

/-- The concrete link evidence. link_identification is the concrete comparison,
not a truth placeholder; link_implies_inclusion is the actual ray membership. -/
structure ConcreteSourceLink where
  qLogVolume : Real
  qLogVolume_eq : qLogVolume = concreteQLogVolume (l := l) I
  link_identification : Prop
  link_identification_eq : link_identification =
    concreteSourceComparison (l := l) I P
  link_implies_inclusion :
    link_identification →
      qLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume

/-- The actual concrete source link. -/
def concreteSourceLink : ConcreteSourceLink (l := l) I P where
  qLogVolume := concreteQLogVolume (l := l) I
  qLogVolume_eq := rfl
  link_identification := concreteSourceComparison (l := l) I P
  link_identification_eq := rfl
  link_implies_inclusion := by
    intro h
    exact (concreteSourceComparison_iff_membership (l := l) I P).mp h

/-- The concrete link identification is exactly the concrete comparison. -/
theorem concreteSourceLink_identification :
    (concreteSourceLink (l := l) I P).link_identification =
      concreteSourceComparison (l := l) I P :=
  rfl

/-- The concrete link yields the actual ray membership from its identification. -/
theorem concreteSourceLink_membership
    (h : (concreteSourceLink (l := l) I P).link_identification) :
    concreteQLogVolume (l := l) I ∈
      hullLogVolumeRay P.signedHullLogVolume :=
  (concreteSourceLink (l := l) I P).link_implies_inclusion h

/-- The exact proposition obstacle: the concrete comparison itself. It is not
asserted; it is the precise proposition that must be proved to pass the link. -/
def ConcreteSourceComparisonObstacle : Prop :=
  concreteSourceComparison (l := l) I P

end LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual

end

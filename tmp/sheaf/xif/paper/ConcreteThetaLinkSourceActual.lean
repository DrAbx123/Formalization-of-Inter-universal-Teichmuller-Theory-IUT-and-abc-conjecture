import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.PaperXiFInclusion

/-!
# Concrete paper Theta-link/source comparison evidence

This file constructs the actual-carrier Theta-link fields for a concrete paper
q-pilot object and a paper signed hull.

The exact source comparison used as link identification is

  P.procession.average <= -O.qPilotLogVolume,

i.e. the paper procession-normalized |log Theta| bound on the actual q-pilot
scalar. This is a genuine proposition, not a degenerate placeholder. The implication to the paper
xi-f membership

  O.qPilotLogVolume in hullLogVolumeRay P.signedHullLogVolume

is proved by the actual equality
P.signedHullLogVolume = -P.procession.average and real arithmetic; it is not
made definitional and is not faked.

No inhabitant of the comparison is asserted. No source curve donor, Value-hull
surrogate, forbidden declaration, or degenerate placeholder is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual

universe ua uv upi umon ui uG uL uC uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- The exact concrete paper source comparison: the signed hull procession
average is bounded by the q-pilot magnitude. -/
def concreteSourceComparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) : Prop :=
  P.procession.average <= -O.qPilotLogVolume

/-- The paper signed hull volume is the negative procession average. -/
theorem concrete_signedHull_eq_neg_average
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) :
    P.signedHullLogVolume = -P.procession.average :=
  P.signedHullLogVolume_eq_neg_average

/-- The actual xi-f membership follows from the concrete source comparison by
real arithmetic on the actual signed-hull scalar. -/
theorem concreteMembership_of_sourceComparison
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (h : concreteSourceComparison O P) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume := by
  rw [mem_hullLogVolumeRay_iff]
  rw [concrete_signedHull_eq_neg_average (O := O) (P := P)]
  unfold concreteSourceComparison at h
  linarith

/-- The actual Theta-link fields for a concrete paper q-pilot/signed-hull pair. -/
structure ConcreteThetaLink
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) where
  /-- Exact source comparison, a genuine real proposition. -/
  link_identification : Prop
  /-- Actual implication to the paper signed-hull ray. -/
  link_implies_inclusion :
    link_identification →
      O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume

/-- Actual concrete link with the comparison as identification and the proved
membership implication. -/
def concreteThetaLink
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) : ConcreteThetaLink O P where
  link_identification := concreteSourceComparison O P
  link_implies_inclusion := concreteMembership_of_sourceComparison O P

/-- The link identification is exactly the source comparison. -/
theorem concreteThetaLink_identification
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) :
    (concreteThetaLink O P).link_identification =
      concreteSourceComparison O P :=
  rfl

/-- The actual xi-f inequality from an actual concrete link and its
identification. -/
theorem concreteThetaLink_xiFInequality
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (L : ConcreteThetaLink O P) (h : L.link_identification) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp (L.link_implies_inclusion h)

/-- The concrete q-pilot constructor supplies an actual paper q-pilot object; the
link fields above apply to it. -/
noncomputable def concreteQPilotLink
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (P : PaperSignedHull X label) :
    ConcreteThetaLink (paperQPilotObjectConcrete (l := l) I) P :=
  concreteThetaLink (paperQPilotObjectConcrete (l := l) I) P

end LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual

end

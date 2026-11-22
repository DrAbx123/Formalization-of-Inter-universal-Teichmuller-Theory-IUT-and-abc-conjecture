import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.PaperXiFInclusion

/-!
# Theta-link from the actual q-pilot object and the paper signed hull

This is the source attempt asked for by task-553.  It uses

* the actual paper q-pilot object PaperQPilotObjectActual of
  QPilotObjectActual.lean, whose signed scalar is
  signedQPilotLogVolume = Real.log ||q|| < 0; and
* the actual PaperSignedHull, whose signed hull log-volume is
  -procession.average with average >= 0

and constructs the two Theta-link fields at this actual carrier:

  link_identification : Prop
  link_implies_inclusion :
    link_identification ->
      O.signedQPilotLogVolume in hullLogVolumeRay P.signedHullLogVolume

The source comparison that is not present in either actual object is:

  P.procession.average <= -O.signedQPilotLogVolume

i.e. the paper's procession-normalized |log Theta| is bounded by the actual
q-pilot |log q|.  This file defines that exact comparison proposition as the
link identification and proves the inclusion from it by real arithmetic.  It
does not assert the comparison; no True/PUnit/axiom/sorry is used.

The existing ThetaLinkActual structure in ThetaLinkActual.lean is indexed by
the older PaperQPilotObject, not by PaperQPilotObjectActual; the actual carrier
here has a different type, so this file provides the actual-carrier version of
the same two fields rather than fabricating a conversion between the two paper
objects.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ThetaLinkFromSource

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui uC3 uD3 uM uP uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-! ## 1. The exact source comparison -/

/-- The exact paper comparison that is missing from the two actual carriers:
the signed hull procession average is at most the q-pilot magnitude. -/
def sourceComparison
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) : Prop :=
  P.procession.average <= -O.signedQPilotLogVolume

/-- Alias used to avoid the section-implicit name clash in this file. -/
abbrev thetaSourceComparison
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) : Prop :=
  P.procession.average <= -O.signedQPilotLogVolume

/-- The paper signed hull volume is the negative of the procession average. -/
theorem signedHull_eq_neg_average
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) :
    P.signedHullLogVolume = -P.procession.average :=
  P.signedHullLogVolume_eq_neg_average

/-- The xi-f membership follows from the exact comparison, with no value-layer
hull-sup and no surrogate carrier. -/
theorem xiFMembership_of_sourceComparison
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label)
    (h : thetaSourceComparison O P) :
    O.signedQPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume := by
  rw [mem_hullLogVolumeRay_iff]
  have hP := P.signedHullLogVolume_eq_neg_average
  unfold thetaSourceComparison at h
  linarith

/-- The signed q-pilot scalar is negative, as required by the paper sign. -/
theorem signedQPilotLogVolume_neg
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I)) :
    O.signedQPilotLogVolume < 0 :=
  O.signedQPilotLogVolume_neg

/-- The signed hull volume is nonpositive. -/
theorem signedHullLogVolume_nonpos
    (P : PaperSignedHull X label) :
    P.signedHullLogVolume <= 0 :=
  PaperSignedHull.signedHullLogVolume_nonpos P

/-! ## 2. The actual-carrier Theta-link fields -/

/-- The two Theta-link fields at the actual q-pilot/signed-hull carriers.  The
identification is a concrete real comparison, not True; the implication is
proved from real arithmetic on the actual scalars. -/
structure ActualThetaLink
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) where
  /-- Exact source comparison: procession average <= q-pilot magnitude. -/
  link_identification : Prop
  /-- Membership in the paper signed hull ray from the link identification. -/
  link_implies_inclusion :
    link_identification ->
      O.signedQPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume

/-- The actual-carrier link with the exact comparison as identification. -/
def actualThetaLink
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) : ActualThetaLink O P where
  link_identification := thetaSourceComparison O P
  link_implies_inclusion := xiFMembership_of_sourceComparison O P

/-- The actual link identification is exactly the source comparison. -/
theorem actualThetaLink_link_identification
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) :
    (actualThetaLink O P).link_identification = thetaSourceComparison O P :=
  rfl

/-- The actual link implication is the xi-f membership theorem. -/
theorem actualThetaLink_link_implies_inclusion
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label)
    (h : thetaSourceComparison O P) :
    (actualThetaLink O P).link_implies_inclusion h =
      xiFMembership_of_sourceComparison O P h :=
  rfl

/-- The actual xi-f inequality from an actual link and its identification. -/
theorem actualThetaLink_xiFInequality
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label)
    (L : ActualThetaLink O P) (h : L.link_identification) :
    O.signedQPilotLogVolume <= P.signedHullLogVolume :=
  (mem_hullLogVolumeRay_iff).mp (L.link_implies_inclusion h)

/-- The exact missing source theorem, stated as a proposition: the paper
procession average is bounded by the actual q-pilot magnitude. -/
def MissingSourceComparison
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP} (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) : Prop :=
  thetaSourceComparison O P

end LeanFormal.IUT.XiFPaper.ThetaLinkFromSource

end
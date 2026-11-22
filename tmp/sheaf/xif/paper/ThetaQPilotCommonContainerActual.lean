import tmp.sheaf.xif.paper.ThetaPilotObjectActual
import tmp.sheaf.xif.paper.QPilotObjectActual

/-!
# Actual common q-pilot / Theta-pilot container

The actual q-pilot point and the actual Theta-pilot image/hull live in the same
actual carrier I.ThetaPilotPoint v:

* qPilotPoint := I.sourceQPilotPoint v R n;
* thetaPilotImage := I.possibleThetaPilotImageSet v R n;
* thetaPilotHull := I.sourceHolomorphicHull v R n.

This file constructs the actual common container carrying these objects, the
actual q-pilot localization into it, the actual Theta-pilot image/hull
localization, and the actual comparison membership qPilotPoint in hull.

This is not a q/scale simplification: the carrier is the source ThetaPilotPoint
carrier, and the sets are the actual source image/hull sets.

No Missing-only, arbitrary data, PUnit/True, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ThetaQPilotCommonContainerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Actual common container for the q-pilot point and Theta-pilot image/hull at
a source place v, realization R and pilot n. -/
structure ActualThetaQPilotCommonContainer
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  carrier : Type
  qPilotPoint : carrier
  thetaPilotImageSet : Set carrier
  thetaPilotHull : Set carrier
  qPilot_mem_hull : qPilotPoint ∈ thetaPilotHull
  image_subset_hull : thetaPilotImageSet ⊆ thetaPilotHull
  image_nonempty : thetaPilotImageSet.Nonempty

/-- The actual common container from the source q-pilot point and Theta-pilot
image/hull. -/
noncomputable def actualThetaQPilotCommonContainer
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    ActualThetaQPilotCommonContainer (I := I) v R n where
  carrier := I.ThetaPilotPoint v
  qPilotPoint := I.sourceQPilotPoint v R n
  thetaPilotImageSet := I.possibleThetaPilotImageSet v R n
  thetaPilotHull := I.sourceHolomorphicHull v R n
  qPilot_mem_hull := by
    change I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l)) ∈
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
    exact I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n
      (oneSignedLabel (l := l))
  image_subset_hull :=
    I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n
  image_nonempty :=
    I.possibleThetaPilotImageSet_nonempty v R n

namespace ActualThetaQPilotCommonContainer

variable (C : ActualThetaQPilotCommonContainer (I := I) v R n)

/-- The actual q-pilot localization into the common carrier. -/
def qPilotLocalization : C.carrier :=
  C.qPilotPoint

/-- The actual Theta-pilot image localization into the common carrier. -/
def thetaPilotImageLocalization : Set C.carrier :=
  C.thetaPilotImageSet

/-- The actual Theta-pilot hull localization into the common carrier. -/
def thetaPilotHullLocalization : Set C.carrier :=
  C.thetaPilotHull

/-- The actual q-pilot point is in the localized hull. -/
theorem qPilotLocalization_mem_hull :
    C.qPilotLocalization ∈ C.thetaPilotHullLocalization :=
  C.qPilot_mem_hull

/-- The actual localized image is contained in the localized hull. -/
theorem thetaPilotImageLocalization_subset_hull :
    C.thetaPilotImageLocalization ⊆ C.thetaPilotHullLocalization :=
  C.image_subset_hull

/-- The actual localized image is nonempty. -/
theorem thetaPilotImageLocalization_nonempty :
    C.thetaPilotImageLocalization.Nonempty :=
  C.image_nonempty

end ActualThetaQPilotCommonContainer

/-- The actual common container's q-pilot point is exactly the source q-pilot
point. -/
@[simp] theorem actual_qPilotPoint (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    (actualThetaQPilotCommonContainer (I := I) v R n).qPilotPoint =
      I.sourceQPilotPoint v R n := rfl

/-- The actual common container's Theta-pilot image is exactly the source image
set. -/
@[simp] theorem actual_thetaPilotImageSet (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    (actualThetaQPilotCommonContainer (I := I) v R n).thetaPilotImageSet =
      I.possibleThetaPilotImageSet v R n := rfl

/-- The actual common container's Theta-pilot hull is exactly the source hull. -/
@[simp] theorem actual_thetaPilotHull (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    (actualThetaQPilotCommonContainer (I := I) v R n).thetaPilotHull =
      I.sourceHolomorphicHull v R n := rfl

end LeanFormal.IUT.XiFPaper.ThetaQPilotCommonContainerActual

end

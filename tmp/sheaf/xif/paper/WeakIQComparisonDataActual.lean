import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual
import tmp.sheaf.xif.paper.ThetaPilotObjectActual

/-!
# Weak IQ comparison data: actual q-pilot and Theta-hull volumes

This file constructs only the data needed for a direct comparison of the
q-pilot log-volume with the Theta-pilot image/hull log-volume:

* the actual q-pilot signed log-volume from the source one-column q;
* the actual Theta-pilot image and holomorphic hull at a place v, realization R
  and pilot n;
* their actual source set-volumes;
* the actual containment image subset hull and the induced volume inequality.

It does NOT construct an IQ carrier equivalence, does not construct a full
multiradial action, and does not prove any q-pilot/Theta hull comparison
inequality beyond the actual image subset hull monotonicity.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.WeakIQComparisonDataActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Actual q-pilot signed log-volume from the source one-column q. -/
def qPilotVolume : Real :=
  I.qPilotSignedLogVolume

/-- The actual q-pilot volume is the source signed q-pilot log. -/
theorem qPilotVolume_eq : qPilotVolume (I := I) = I.qPilotSignedLogVolume := rfl

/-- Actual Theta-pilot image set at v,R,n. -/
def thetaPilotImage : Set (I.ThetaPilotPoint v) :=
  I.possibleThetaPilotImageSet v R n

/-- Actual Theta-pilot hull at v,R,n. -/
def thetaPilotHull : Set (I.ThetaPilotPoint v) :=
  I.sourceHolomorphicHull v R n

/-- The actual Theta-pilot image is contained in the actual hull. -/
theorem thetaPilotImage_subset_hull :
    thetaPilotImage (I := I) v R n ⊆ thetaPilotHull (I := I) v R n :=
  I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n

/-- Actual source volume of the Theta-pilot image. -/
def thetaPilotImageVolume : ENNReal :=
  I.sourceSetVolume v (thetaPilotImage (I := I) v R n)

/-- Actual source volume of the Theta-pilot hull. -/
def thetaPilotHullVolume : ENNReal :=
  I.sourceSetVolume v (thetaPilotHull (I := I) v R n)

/-- The actual image volume is at most the actual hull volume. -/
theorem thetaPilotImageVolume_le_hullVolume :
    thetaPilotImageVolume (I := I) v R n ≤
      thetaPilotHullVolume (I := I) v R n :=
  I.sourceSetVolume_mono v (thetaPilotImage_subset_hull (I := I) v R n)

/-- Weak IQ comparison data: q-pilot volume and Theta-pilot image/hull volumes. -/
structure WeakIQComparisonData where
  qPilotVolume : Real
  thetaImage : Set (I.ThetaPilotPoint v)
  thetaHull : Set (I.ThetaPilotPoint v)
  thetaImage_subset_hull : thetaImage ⊆ thetaHull
  thetaImageVolume : ENNReal
  thetaHullVolume : ENNReal
  thetaImageVolume_eq : thetaImageVolume = I.sourceSetVolume v thetaImage
  thetaHullVolume_eq : thetaHullVolume = I.sourceSetVolume v thetaHull
  thetaImageVolume_le_hullVolume : thetaImageVolume ≤ thetaHullVolume

/-- The actual weak IQ comparison data from q-pilot and Theta-pilot sets. -/
noncomputable def weakIQComparisonData : WeakIQComparisonData (I := I) v where
  qPilotVolume := qPilotVolume (I := I)
  thetaImage := thetaPilotImage (I := I) v R n
  thetaHull := thetaPilotHull (I := I) v R n
  thetaImage_subset_hull := thetaPilotImage_subset_hull (I := I) v R n
  thetaImageVolume := thetaPilotImageVolume (I := I) v R n
  thetaHullVolume := thetaPilotHullVolume (I := I) v R n
  thetaImageVolume_eq := rfl
  thetaHullVolume_eq := rfl
  thetaImageVolume_le_hullVolume :=
    thetaPilotImageVolume_le_hullVolume (I := I) v R n

/-- The constructed q-pilot volume is the source signed q-pilot log. -/
@[simp] theorem weakIQComparisonData_qPilotVolume :
    (weakIQComparisonData (I := I) v R n).qPilotVolume =
      I.qPilotSignedLogVolume := rfl

/-- The constructed Theta-pilot image volume is the source image volume. -/
@[simp] theorem weakIQComparisonData_thetaImageVolume :
    (weakIQComparisonData (I := I) v R n).thetaImageVolume =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := rfl

/-- The constructed Theta-pilot hull volume is the source hull volume. -/
@[simp] theorem weakIQComparisonData_thetaHullVolume :
    (weakIQComparisonData (I := I) v R n).thetaHullVolume =
      I.sourceSetVolume v (I.sourceHolomorphicHull v R n) := rfl

end LeanFormal.IUT.XiFPaper.WeakIQComparisonDataActual

end
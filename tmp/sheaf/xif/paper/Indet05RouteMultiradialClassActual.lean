import tmp.sheaf.xif.paper.S3139SourceMultiradialQuotientActual
import tmp.sheaf.xif.paper.S3138SourceProcessionCoreActual
import tmp.sheaf.xif.paper.Indet01FirstTriangleIndActual
import tmp.sheaf.xif.paper.Indet02BPSMultiradialUpToActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Indet05: route-side multiradial class up to (Ind1),(Ind2), (Ind3) one-sided

The route's own multiradial layer (S3139SourceMultiradialQuotientActual) already
proves that the descended multiradial map is (Ind1)/(Ind2)-invariant, that the
descended log-volume is monotone under the (Ind3) direction, that the quotient
level increases by n under (Ind3), and the (Ind3) possible-image upper-semi law.
This file re-exposes those as the route-side indeterminacy statement layer and
ties it to the A35 first-triangle layer (Indet01/Indet02).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Indet05RouteMultiradialClassActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.Indet01FirstTriangleIndActual
open LeanFormal.IUT.XiFPaper.Indet02BPSMultiradialUpToActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-- Route-side (Ind1) invariance of the descended multiradial representation. -/
theorem routeMultiradial_ind1
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (g : SourceStepXILabel) (c : SourceStepXIChoice I) :
    sourceMultiradialMap I ((sourceStepXICore I).ind1 g c) =
      sourceMultiradialMap I c :=
  sourceMultiradialMap_ind1 I g c

/-- Route-side (Ind2) invariance of the descended multiradial representation. -/
theorem routeMultiradial_ind2
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (g : SourceStepXILabel) (c : SourceStepXIChoice I) :
    sourceMultiradialMap I ((sourceStepXICore I).ind2 g c) =
      sourceMultiradialMap I c :=
  sourceMultiradialMap_ind2 I g c

/-- Route-side (Ind3) one-sided log-volume monotonicity. -/
theorem routeMultiradial_ind3_logVolume_le
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Nat)
    (c : SourceStepXIChoice I) :
    sourceMultiradialLogVolume I (sourceMultiradialMap I c) ≤
      sourceMultiradialLogVolume I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c)) :=
  sourceMultiradialLogVolume_ind3_le I n c

/-- Route-side (Ind3) level increase: the quotient level grows by n. -/
theorem routeMultiradial_ind3_level
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Nat)
    (c : SourceStepXIChoice I) :
    sourceMultiradialLevel I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c)) =
      sourceMultiradialLevel I (sourceMultiradialMap I c) + n :=
  sourceMultiradialLevel_ind3 I n c

/-- Route-side (Ind3) possible-image upper-semi. -/
theorem routeMultiradial_ind3_possibleImage_upper
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Nat)
    (c : SourceStepXIChoice I) (z : ℝ)
    (hz : z ∈ sourceMultiradialPossibleImage I (sourceMultiradialMap I c)) :
    ∃ w, w ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 n c)) ∧ z ≤ w :=
  sourceMultiradialPossibleImage_ind3_upper I n c z hz

/-- The route-side up-to structure: the invariant object is the quotient class;
(Ind1)/(Ind2) act trivially and (Ind3) is one-sided. -/
structure RouteMultiradialUpTo
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- a chosen source representative of the multiradial representation -/
  representative : SourceStepXIChoice I

/-- The invariant class of a route multiradial representation. -/
def RouteMultiradialUpTo.repClass
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (x : RouteMultiradialUpTo I) : SourceMultiradialCarrier I :=
  sourceMultiradialMap I x.representative

/-- The class is independent of the representative up to (Ind1),(Ind2). -/
theorem RouteMultiradialUpTo.repClass_congr
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    (x y : RouteMultiradialUpTo I)
    (h : sourceMultiradialMap I x.representative =
      sourceMultiradialMap I y.representative) :
    x.repClass = y.repClass := h

/-- A35/route anchor table: route multiradial indeterminacy statements. -/
def routeIndeterminacyA35Anchors : List (String × String) :=
  [ ("route (Ind1) invariance", "Indet05.routeMultiradial_ind1 (from sourceMultiradialMap_ind1)"),
    ("route (Ind2) invariance", "Indet05.routeMultiradial_ind2 (from sourceMultiradialMap_ind2)"),
    ("route (Ind3) one-sided log-volume", "Indet05.routeMultiradial_ind3_logVolume_le"),
    ("route (Ind3) level increase", "Indet05.routeMultiradial_ind3_level"),
    ("route (Ind3) possible-image upper-semi", "Indet05.routeMultiradial_ind3_possibleImage_upper"),
    ("up-to class object", "Indet05.RouteMultiradialUpTo.repClass_congr"),
    ("A35 first-triangle layer", "Indet01/Indet02 (Ind1/Ind2 quotient; Ind3 one-sided), Audit IUT-III.Ind1/2/3 PENDING"),
    ("corpus", "IUT III 653-679; MHYY Formalization of IUT (2026-04) §4 472-501") ]

end LeanFormal.IUT.XiFPaper.Indet05RouteMultiradialClassActual

end

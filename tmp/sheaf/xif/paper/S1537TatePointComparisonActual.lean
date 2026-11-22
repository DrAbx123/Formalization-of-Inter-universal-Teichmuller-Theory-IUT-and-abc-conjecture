import tmp.sheaf.xif.paper.S1515KSideTateRealizesCurveActual

/-! # S1537: K-side Tate point comparison from the F-side comparison

S1515 supplies the actual coordinate change and realizesCurve equality.  The
remaining field is exactly the K-side Tate point comparison
  TatePointComparison (kSideCurve T) (sectionKPlace T b) (sectionQ T b).

The F-side clause-(b) comparison lives over Completion (sectionFPlace T b);
the K-side comparison lives over Completion (sectionKPlace T b).  Its
pointEquiv compares the local-unit quotient of AlgebraicClosure(K_v) with the
algebraic-closure points of the base-changed K-side curve.  No map of
algebraic closures from F_v to K_v (or point-comparison transport along
completionMap) exists in the tree, so the point comparison cannot be
transported from F-side points; it is recorded as the exact first missing
point comparison, not replaced by an ambient/proxy comparison.

Conditional constructors below fill S1498RemainingTransport and
S1482KSideTateData from the missing point comparison, using only the actual
S1515 algebraic fields.  No Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual
open LeanFormal.IUT.XiFPaper.S1498KSideTateTransportActual
open LeanFormal.IUT.XiFPaper.S1515KSideTateRealizesCurveActual

namespace LeanFormal.IUT.XiFPaper.S1537TatePointComparisonActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The exact missing K-side point comparison. -/
abbrev S1537KPointComparison : Type _ :=
  TatePointComparison (kSideCurve (T := T))
    (sectionKPlace T b) (sectionQ T b)

/-- Conditional construction of the remaining S1498 transport from the actual
coordinate change/realizesCurve and the missing point comparison. -/
noncomputable def s1537S1498RemainingTransport
    (h : S1537KPointComparison T b) :
    S1498RemainingTransport (T := T) (b := b) where
  canonicalIsElliptic := canonicalIsElliptic T b
  realizesCurve := s1498RealizesCurveTarget T b
  points := h

/-- Conditional construction of the S1482 K-side Tate data from the actual
coordinate change/realizesCurve and the missing point comparison. -/
noncomputable def s1537S1482KSideTateData
    (h : S1537KPointComparison T b) :
    S1482KSideTateData T b where
  canonicalIsElliptic := canonicalIsElliptic T b
  coordinateChange := s1498CoordinateChange (T := T) (b := b)
  realizesCurve := s1498RealizesCurveTarget T b
  points := h

/-- Exact first missing field: the K-side point comparison type itself. -/
def s1537FirstMissingPointComparison
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Type _ :=
  S1537KPointComparison T b

end LeanFormal.IUT.XiFPaper.S1537TatePointComparisonActual

end

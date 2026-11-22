import tmp.sheaf.xif.paper.S1444ReportAKPlaceQActual
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary

/-! # S1482: K-side Tate uniformization, exact first fields

S1444 supplies the F-side clause-(b) TateCurveComparison at sectionFPlace and
the K-side q = sectionQ (completionMap image).  The K-side object
TateCurveComparison (kSideCurve T) (sectionKPlace T b) (sectionQ T b) requires
a variable change over the K-completion, the curve realization, and the point
comparison.  No base-change transport of the F-side comparison to the
section K-place is constructed in the tree; this file records those exact
fields without ambient/proxy substitution. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing data for the K-side TateCurveComparison. -/
structure S1482KSideTateData where
  canonicalIsElliptic :
    (TateCurve.weierstrassCurve (Completion (sectionKPlace T b))
      (sectionQ T b).q).IsElliptic
  coordinateChange :
    WeierstrassCurve.VariableChange (Completion (sectionKPlace T b))
  realizesCurve :
    coordinateChange • TateCurve.weierstrassCurve
        (Completion (sectionKPlace T b)) (sectionQ T b).q =
      ((kSideCurve (T := T)).baseChange
        (Completion (sectionKPlace T b))).curve
  points : TatePointComparison (kSideCurve (T := T))
    (sectionKPlace T b) (sectionQ T b)

/-- Projection from an actual comparison to the exact data. -/
noncomputable def S1482KSideTateDataOfComparison
    (C : TateCurveComparison (kSideCurve (T := T))
      (sectionKPlace T b) (sectionQ T b)) : S1482KSideTateData T b where
  canonicalIsElliptic := C.canonicalIsElliptic
  coordinateChange := C.coordinateChange
  realizesCurve := C.realizesCurve
  points := C.points

/-- The exact target type. -/
abbrev S1482KSideTateComparison : Type _ :=
  TateCurveComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b)

end LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual
end
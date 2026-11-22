import tmp.sheaf.xif.paper.S1482KSideTateUniformizationActual
import tmp.sheaf.xif.paper.S1444ReportAKPlaceQActual
import LeanFormal.IUT.Foundations.Geometry.TateCurvePointMap

/-! # S1498: F-side to K-side Tate transport, exact first transport

The actual F-side comparison C_F exists (S1444).  The actual completionMap
Completion sectionFPlace -> Completion sectionKPlace exists.  This file fills
the coordinate-change transport (VariableChange.map) and records the exact
remaining transport fields: realizesCurve and the Tate point comparison.  No
ambient/proxy comparison is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1498KSideTateTransportActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1444ReportAKPlaceQActual
open LeanFormal.IUT.XiFPaper.S1482KSideTateUniformizationActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual ring hom from the F-completion to the K-completion. -/
noncomputable def s1498CompletionMap :
    Completion (sectionFPlace T b) →+* Completion (sectionKPlace T b) :=
  completionMap (k := T.arithmetic.F) (sectionKPlace T b)

/-- Actual coordinate change transported from the F-side comparison. -/
noncomputable def s1498CoordinateChange :
    WeierstrassCurve.VariableChange (Completion (sectionKPlace T b)) :=
  (sectionTateWitness_comparison T b).coordinateChange.map
    (s1498CompletionMap (T := T) (b := b))

/-- Exact realizesCurve target after the coordinate-change transport. -/
def S1498RealizesCurveTarget : Prop :=
  s1498CoordinateChange (T := T) (b := b) •
      TateCurve.weierstrassCurve (Completion (sectionKPlace T b)) (sectionQ T b).q =
    ((kSideCurve (T := T)).baseChange
      (Completion (sectionKPlace T b))).curve

/-- Exact remaining transport data after the actual coordinate change. -/
structure S1498RemainingTransport where
  canonicalIsElliptic :
    (TateCurve.weierstrassCurve (Completion (sectionKPlace T b))
      (sectionQ T b).q).IsElliptic
  realizesCurve : s1498CoordinateChange (T := T) (b := b) •
      TateCurve.weierstrassCurve (Completion (sectionKPlace T b)) (sectionQ T b).q =
    ((kSideCurve (T := T)).baseChange
      (Completion (sectionKPlace T b))).curve
  points : TatePointComparison (kSideCurve (T := T))
    (sectionKPlace T b) (sectionQ T b)

/-- Exact first missing transport: the realizesCurve equality above. -/
def S1498FirstMissingTransport : Prop :=
  S1498RealizesCurveTarget (T := T) (b := b)

end LeanFormal.IUT.XiFPaper.S1498KSideTateTransportActual
end
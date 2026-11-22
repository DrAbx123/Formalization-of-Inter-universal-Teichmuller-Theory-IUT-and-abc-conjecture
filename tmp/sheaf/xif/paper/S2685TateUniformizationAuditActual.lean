import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual

namespace LeanFormal.IUT.XiFPaper.S2685TateUniformizationAuditActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual reusable CurveIndexedTateUniformization at the section K-place,
obtained from the actual F-side comparison and the closure base-change
transport.  This is the constructor available in the current tree; it is not
the missing concrete q = 5 analytic constructor. -/
noncomputable def S2685CurveIndexedTateUniformizationAtSection :
    CurveIndexedTateUniformization (kSideCurve (T := T))
      (sectionKPlace T b) (sectionQ T b) :=
  (tateCurveComparison (T := T) (b := b)).toUniformization

theorem S2685_nonempty_atSection :
    Nonempty (CurveIndexedTateUniformization (kSideCurve (T := T))
      (sectionKPlace T b) (sectionQ T b)) :=
  ⟨S2685CurveIndexedTateUniformizationAtSection T b⟩

#check S2685CurveIndexedTateUniformizationAtSection
#check S2685_nonempty_atSection
#print axioms S2685_nonempty_atSection

end LeanFormal.IUT.XiFPaper.S2685TateUniformizationAuditActual
end

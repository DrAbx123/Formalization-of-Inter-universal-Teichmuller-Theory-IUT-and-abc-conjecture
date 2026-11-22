import tmp.sheaf.xif.paper.S2070CurveEtaleFundamentalCardActual
import tmp.sheaf.xif.paper.S2073FiniteGroupQuotientActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2080CurveQuotientsTransportActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual
open LeanFormal.IUT.XiFPaper.S2073FiniteGroupQuotientActual

/-- M1 reduction: the S2073 affine-base cocone colimit gives the exact
CurveQuotientsByFiniteGroups obligation. -/
theorem s2080_curveQuotients_of_affine {K : Type*} [Field K]
    (h : S2073AffineActionCoconeIsColimit (curveCoordinateRing K)) :
    CurveQuotientsByFiniteGroups K := by
  intro G _ _
  have hq := S2073curveHasQuotients_of_affine (K := K) h
  exact hq G

end LeanFormal.IUT.XiFPaper.S2080CurveQuotientsTransportActual
end
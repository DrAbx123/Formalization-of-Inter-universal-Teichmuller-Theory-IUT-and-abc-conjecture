import tmp.sheaf.xif.paper.S1575CurvePolyMapActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual

/-! # S1589: retry report for omega/psi_c/dblZ

S1521 supplies WeierstrassCurve.ω_spec; S1410 supplies map_ω and map_ψc.
The explicit-map statements were attempted, but the target on the nested
Poly = Polynomial (Polynomial (MvPolynomial Coeff ℤ)) still hits an isDefEq
timeout.  This file records the exact available inputs and does not fake a map.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1589CurvePolyOmegaRetryActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal

#check WeierstrassCurve.ω_spec
#check WeierstrassCurve.map_ω
#check WeierstrassCurve.map_ψc
#check WeierstrassCurve.ψ_mul_ψc
#check S1575MapOmegaMissing
#check S1575MapPsiCMissing
#check S1575DblZSmulPolyMissing

/-- Exact dblZ target, unchanged. -/
def S1589DblZRequired : Prop :=
  forall n : Int,
    WeierstrassCurve.Jacobian.dblZ curvePoly.toAffine (smulPoly n) =
      curve.ψ (2 * n)

end LeanFormal.IUT.XiFPaper.S1589CurvePolyOmegaRetryActual
end
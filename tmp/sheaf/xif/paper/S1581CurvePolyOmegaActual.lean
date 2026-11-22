import tmp.sheaf.xif.paper.S1575CurvePolyMapActual

/-! # S1581: omega/psi_c/dblZ elaboration report

S1410 already has the source naturality lemmas map_ω and map_ψc.  Their
S1575 target statements are definitionally those lemmas, but elaborating the
target on the nested Poly = Polynomial (Polynomial (MvPolynomial Coeff ℤ))
hits a deterministic isDefEq timeout even at maxHeartbeats 8,000,000 and
synthInstance.maxHeartbeats 8,000,000.  The dblZ identity additionally needs
the omega defining identity (S1509/S1521 first missing input).  This file
records the exact targets; it does not fake a map. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1581CurvePolyOmegaActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal

#check S1575MapOmegaMissing
#check S1575MapPsiCMissing
#check S1575DblZSmulPolyMissing
#check curvePoly
#check curvePoly_φ
#check curvePoly_ψ

end LeanFormal.IUT.XiFPaper.S1581CurvePolyOmegaActual
end
import tmp.sheaf.xif.paper.S1589CurvePolyOmegaRetryActual
import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
/-! # S1591: map_omega/map_psi_c via simp only, no isDefEq hang
`exact WeierstrassCurve.map_ω` hits an isDefEq hang on nested Poly.  The tactic
`simp only [curvePoly, polyMap, WeierstrassCurve.map_ω]` succeeds.  Same for
map_ψc.  dblZ_smulPoly remains the exact next missing (it additionally needs the
omega defining identity and TauCeti's dblZ_smulPoly). -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1591MapOmegaTacticRetryActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
theorem s1591MapOmega : S1575MapOmegaMissing := by
  intro n
  simp only [curvePoly, polyMap, WeierstrassCurve.map_ω]
theorem s1591MapPsiC : S1575MapPsiCMissing := by
  intro n
  simp only [curvePoly, polyMap, WeierstrassCurve.map_ψc]
end LeanFormal.IUT.XiFPaper.S1591MapOmegaTacticRetryActual
end

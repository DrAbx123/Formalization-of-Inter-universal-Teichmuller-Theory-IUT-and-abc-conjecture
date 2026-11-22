import tmp.sheaf.xif.paper.S1589CurvePolyOmegaRetryActual
import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
/-! # S1590: nested Poly workaround diagnostic
Poly2/polyMap2 with explicit codomain annotations and ascriptions make the
omega/psi_c types match definitionally (checked below), but the proof term
`exact WeierstrassCurve.map_ω ...` still triggers a deterministic isDefEq hang
on the nested Poly = Polynomial (Polynomial (MvPolynomial Coeff Z)).  This file
records the minimal reproduction; it does not fake the identity. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1590CurvePolyOmegaWorkaroundActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
open WeierstrassCurve.Universal
abbrev Poly2 : Type := Polynomial (Polynomial (MvPolynomial Coeff ℤ))
abbrev polyMap2 : MvPolynomial Coeff ℤ →+* Poly2 :=
  (Polynomial.C : Polynomial (MvPolynomial Coeff ℤ) →+* Poly2).comp
    (Polynomial.C : MvPolynomial Coeff ℤ →+* Polynomial (MvPolynomial Coeff ℤ))
#check (fun n : ℤ => (curve.ω n))
#check (fun n : ℤ => (curve.ω n).map (mapRingHom polyMap2))
#check (fun n : ℤ => ((curve.map polyMap2 : WeierstrassCurve Poly2)).ω n)
#check (fun n : ℤ => (curve.ψc n))
#check (fun n : ℤ => (curve.ψc n).map (mapRingHom polyMap2))
#check (fun n : ℤ => ((curve.map polyMap2 : WeierstrassCurve Poly2)).ψc n)
#check S1575MapOmegaMissing
#check S1575MapPsiCMissing
#check S1575DblZSmulPolyMissing
end LeanFormal.IUT.XiFPaper.S1590CurvePolyOmegaWorkaroundActual
end

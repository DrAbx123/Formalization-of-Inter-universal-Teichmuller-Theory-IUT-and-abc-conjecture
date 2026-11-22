import LeanFormal.IUT.ABCBridge.Geometry.LegendreLevelTwoStructure
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVProp18CompositeActual — IUT IV Prop 1.8 Legendre/2-torsion composite

Genuine composite of the existing Legendre-model assets: the displayed
two-torsion polynomial and its discriminant, the excluded parameter values
forced by ellipticity, and the 2-division evaluation criterion.
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVProp18CompositeActual

open LeanFormal.IUT

theorem iutIVProp18_legendre_twoTorsion_composite {K : Type*} [Field K]
    (parameter : K) [(legendreWeierstrassCurve parameter).IsElliptic] :
    ((legendreWeierstrassCurve parameter).twoTorsionPolynomial =
        ⟨4, -4 * (1 + parameter), 4 * parameter, 0⟩) ∧
      ((legendreWeierstrassCurve parameter).twoTorsionPolynomial.discr =
        256 * (parameter * (1 - parameter)) ^ 2) ∧
      parameter ≠ 0 ∧ parameter ≠ 1 ∧
      (∀ x y : K, (legendreWeierstrassCurve parameter).evalDivisionPolynomial x y 2 = 0 ↔
        (2 : K) * y = 0) :=
  ⟨legendreWeierstrassCurve_twoTorsionPolynomial parameter,
   legendreWeierstrassCurve_twoTorsionPolynomial_discr parameter,
   (legendreWeierstrassCurve_parameters_of_isElliptic parameter
     (by infer_instance)).1,
   (legendreWeierstrassCurve_parameters_of_isElliptic parameter
     (by infer_instance)).2,
   fun x y => legendreWeierstrassCurve_evalDivisionPolynomial_two_eq_zero_iff parameter x y⟩

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVProp18CompositeActual

end

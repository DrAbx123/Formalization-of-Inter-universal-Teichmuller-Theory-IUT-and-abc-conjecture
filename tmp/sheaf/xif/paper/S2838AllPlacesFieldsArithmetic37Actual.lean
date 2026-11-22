import tmp.sheaf.xif.paper.S2837PlaceSelectionArithmetic37Actual
import tmp.sheaf.xif.paper.S2490RestrictionSectionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2837PlaceSelectionArithmetic37Actual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

local instance s2838GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2838AllPlacesFieldsArithmetic37Actual

/-- The full 8-field place block over arithmetic37, using the generic
restriction section of NumberFieldPlace. -/
noncomputable def S2838AllPlacesFields : S2490AllPlacesFields A37 where
  V := S2837PlaceSelection.V
  V_mod_bad := S2837PlaceSelection.V_mod_bad
  V_mod_bad_odd_residue_characteristic :=
    S2837PlaceSelection.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := S2837PlaceSelection.V_mod_bad_nonempty
  V_section := S2837PlaceSelection.V_section
  V_eq_section := rfl
  V_mod_bijection := S2837PlaceSelection.V_mod_bijection
  V_place_comap := by
    intro v
    exact S2837PlaceSelection.V_mod_bijection_symm_apply v

#check S2838AllPlacesFields
#print axioms S2838AllPlacesFields

end LeanFormal.IUT.XiFPaper.S2838AllPlacesFieldsArithmetic37Actual
end

import tmp.sheaf.xif.paper.S2841A6PlaceSelectionActual
import tmp.sheaf.xif.paper.S2490RestrictionSectionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2841A6PlaceSelectionActual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

local instance s2842A6GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2842A6AllPlacesFieldsActual

/-- Generic section F6 -> K for A6. -/
noncomputable def S2842A6Section :
    NumberFieldPlace.RestrictionSection S2847A6.Fmod S2847A6.K :=
  NumberFieldPlace.restrictionSection

/-- The full 8-field place block for A6. -/
noncomputable def S2842A6AllPlacesFields : S2490AllPlacesFields S2847A6 where
  V := S2842A6Section.selected
  V_mod_bad := S2841PlaceSelection.V_mod_bad
  V_mod_bad_odd_residue_characteristic :=
    S2841PlaceSelection.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := S2841PlaceSelection.V_mod_bad_nonempty
  V_section := S2842A6Section
  V_eq_section := rfl
  V_mod_bijection := S2842A6Section.selectedEquiv
  V_place_comap := by
    intro v
    exact NumberFieldPlace.RestrictionSection.selectedEquiv_symm_apply
      S2842A6Section v

#check S2842A6AllPlacesFields
#print axioms S2842A6AllPlacesFields

end LeanFormal.IUT.XiFPaper.S2842A6AllPlacesFieldsActual
end

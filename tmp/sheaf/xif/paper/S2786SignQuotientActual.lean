import tmp.sheaf.xif.paper.S2782Curve37a1Actual
import tmp.sheaf.xif.paper.S2786E37PrimeIdealsActual
import tmp.sheaf.xif.paper.S2490RestrictionSectionActual
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual
open LeanFormal.IUT.XiFPaper.S2786E37PrimeIdealsActual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2786SignQuotientActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance S2786E37QiIsElliptic : E37Qi.IsElliptic := by
  change (E37.map (algebraMap ℚ GaussianField)).IsElliptic
  infer_instance

/-- The punctured Gaussian base change of 37a1. -/
noncomputable def E37QiPunctured : PuncturedEllipticCurve GaussianField where
  curve := E37Qi
  isElliptic := inferInstance
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

/-- Gaussian arithmetic with Fmod = F = K = Q(i), curve 37a1/Q(i). -/
noncomputable def S2786Arithmetic : InitialThetaArithmeticData S2771FiveLabel where
  Fmod := GaussianField
  F := GaussianField
  K := GaussianField
  tower := gaussianIdentityThetaTower S2771FiveLabel
  curve := E37QiPunctured

/-- The two Gaussian places above 37. -/
def S2786VmodBad : Set (NumberField.FinitePlace GaussianField) :=
  {gaussianField37PlusPlace, gaussianField37MinusPlace}

theorem S2786VmodBad_odd :
    ∀ p, p ∈ S2786VmodBad → Odd (NumberFieldFinitePlace.residueCharacteristic p) := by
  intro p hp
  simp only [S2786VmodBad, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact gaussianField37PlusPlace_residueCharacteristic_odd
  · exact gaussianField37MinusPlace_residueCharacteristic_odd

theorem S2786VmodBad_nonempty : S2786VmodBad.Nonempty :=
  ⟨gaussianField37PlusPlace, by simp [S2786VmodBad]⟩

/-- The canonical all-places restriction section for the identity extension
Q(i)/Q(i). -/
noncomputable def S2786Section : NumberFieldPlace.RestrictionSection
    GaussianField GaussianField :=
  NumberFieldPlace.restrictionSection

/-- The 8-field place block of SourceSignQuotientData for E37/Q(i), with the
two prime places above 37 in V_mod_bad. -/
noncomputable def S2786PlaceFields :
    S2490AllPlacesFields S2786Arithmetic where
  V := S2786Section.selected
  V_mod_bad := S2786VmodBad
  V_mod_bad_odd_residue_characteristic := S2786VmodBad_odd
  V_mod_bad_nonempty := S2786VmodBad_nonempty
  V_section := S2786Section
  V_eq_section := rfl
  V_mod_bijection := S2786Section.selectedEquiv
  V_place_comap := by
    intro v
    exact (NumberFieldPlace.RestrictionSection.selectedEquiv_symm_apply
      S2786Section v).symm

#check E37QiPunctured
#check S2786Arithmetic
#check S2786VmodBad
#check S2786PlaceFields
#print axioms S2786VmodBad_odd
#print axioms S2786PlaceFields

end LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
end

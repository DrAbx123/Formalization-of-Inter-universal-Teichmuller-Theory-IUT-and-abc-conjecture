import tmp.sheaf.xif.paper.S2786SignQuotientActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786E37PrimeIdealsActual
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual

/-- The plus place viewed in Fmod = Q(i). -/
def S2786PlusPlace : NumberField.FinitePlace S2786Arithmetic.Fmod := gaussianField37PlusPlace

/-- The minus place viewed in Fmod = Q(i). -/
def S2786MinusPlace : NumberField.FinitePlace S2786Arithmetic.Fmod := gaussianField37MinusPlace

/-- Singleton place selection at the plus prime above 37. -/
noncomputable def S2786PlusSelection : SourcePlaceSelection S2786Arithmetic where
  V_mod_bad := {S2786PlusPlace}
  V_mod_bad_odd_residue_characteristic := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact gaussianField37PlusPlace_residueCharacteristic_odd
  V_mod_bad_nonempty := ⟨S2786PlusPlace, by simp⟩

/-- Singleton place selection at the minus prime above 37. -/
noncomputable def S2786MinusSelection : SourcePlaceSelection S2786Arithmetic where
  V_mod_bad := {S2786MinusPlace}
  V_mod_bad_odd_residue_characteristic := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact gaussianField37MinusPlace_residueCharacteristic_odd
  V_mod_bad_nonempty := ⟨S2786MinusPlace, by simp⟩

/-- The combined two-prime place selection above 37. -/
noncomputable def S2786PlaceSelection : SourcePlaceSelection S2786Arithmetic where
  V_mod_bad := S2786VmodBad
  V_mod_bad_odd_residue_characteristic := S2786VmodBad_odd
  V_mod_bad_nonempty := S2786VmodBad_nonempty

/-- The 8-field place block for E37/Q(i), with the two prime places above 37. -/
noncomputable def S2786PlaceBlock : S2490AllPlacesFields S2786Arithmetic :=
  S2786PlaceFields

@[simp] theorem S2786PlaceSelection_V_mod_bad :
    S2786PlaceSelection.V_mod_bad = S2786VmodBad := rfl

@[simp] theorem S2786PlusSelection_V_mod_bad :
    S2786PlusSelection.V_mod_bad = {S2786PlusPlace} := rfl

@[simp] theorem S2786MinusSelection_V_mod_bad :
    S2786MinusSelection.V_mod_bad = {S2786MinusPlace} := rfl

@[simp] theorem S2786PlaceBlock_V_mod_bad :
    S2786PlaceBlock.V_mod_bad = S2786VmodBad := rfl

#check S2786PlusSelection
#check S2786MinusSelection
#check S2786PlaceSelection
#check S2786PlaceBlock
#print axioms S2786PlusSelection
#print axioms S2786PlaceBlock

end LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
end

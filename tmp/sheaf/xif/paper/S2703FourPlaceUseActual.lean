import tmp.sheaf.xif.paper.S2703FourPlaceDataActual
import tmp.sheaf.xif.paper.S2702FourPlaceInterfaceActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2703FourPlaceUseActual

local instance s2703UseGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The concrete four-place Vbad set. -/
def S2703Vbad : Set (NumberField.FinitePlace GaussianField) :=
  S2696Vbad S2703FourPlaceData

theorem S2703Vbad_finite : S2703Vbad.Finite :=
  S2696Vbad_finite S2703FourPlaceData

theorem S2703Vbad_nonempty : S2703Vbad.Nonempty :=
  S2696Vbad_nonempty S2703FourPlaceData

theorem S2703Vbad_odd :
    ∀ p, p ∈ S2703Vbad →
      Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  S2696Vbad_odd S2703FourPlaceData

noncomputable def S2703Selection (l : PrimeGeFive) :
    SourcePlaceSelection (S1280Arithmetic l) :=
  S2696Selection l S2703FourPlaceData

noncomputable def S2703BadQAbsLog
    (q : (p : NumberField.FinitePlace GaussianField) → p ∈ S2703Vbad → Real) :
    Real :=
  S2696BadQAbsLog S2703FourPlaceData q

#check S2703Vbad
#check S2703Vbad_finite
#check S2703Vbad_nonempty
#check S2703Vbad_odd
#check S2703Selection
#check S2703BadQAbsLog
#print axioms S2703Vbad_odd
#print axioms S2703Selection
end LeanFormal.IUT.XiFPaper.S2703FourPlaceUseActual
end

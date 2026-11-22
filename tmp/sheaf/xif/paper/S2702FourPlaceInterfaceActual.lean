import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2697Two2161PlacesActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2697Two2161PlacesActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2702FourPlaceInterfaceActual

local instance s2702GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Build the canonical S2696FourPlaceData from two explicit places above 5
(with residue characteristic proofs 5) and the two explicit places above 2161
from S2697Two2161PlacesActual (with residue characteristic proofs 2161).
No q candidates are needed: they come from finitePlaceQCandidate_nonempty. -/
noncomputable def S2702FourPlaceData
    (p5a p5b : NumberField.FinitePlace GaussianField)
    (h5a : NumberFieldFinitePlace.residueCharacteristic p5a = 5)
    (h5b : NumberFieldFinitePlace.residueCharacteristic p5b = 5)
    (hplus : NumberFieldFinitePlace.residueCharacteristic
      S2697GaussianPlacePlus = 2161)
    (hminus : NumberFieldFinitePlace.residueCharacteristic
      S2697GaussianPlaceMinus = 2161) :
    S2696FourPlaceData where
  p5a := p5a
  p5b := p5b
  p2161a := S2697GaussianPlacePlus
  p2161b := S2697GaussianPlaceMinus
  odd5a := by rw [h5a]; norm_num
  odd5b := by rw [h5b]; norm_num
  odd2161a := by rw [hplus]; norm_num
  odd2161b := by rw [hminus]; norm_num

/-- The same builder with the 2161 residue-characteristic proof packaged as the
S2697 proposition. -/
noncomputable def S2702FourPlaceDataOfResidue
    (p5a p5b : NumberField.FinitePlace GaussianField)
    (h5a : NumberFieldFinitePlace.residueCharacteristic p5a = 5)
    (h5b : NumberFieldFinitePlace.residueCharacteristic p5b = 5)
    (h2161 : S2697ResidueCharacteristic2161) : S2696FourPlaceData :=
  S2702FourPlaceData p5a p5b h5a h5b h2161.1 h2161.2

#check S2702FourPlaceData
#check S2702FourPlaceDataOfResidue
#print axioms S2702FourPlaceData
end LeanFormal.IUT.XiFPaper.S2702FourPlaceInterfaceActual
end

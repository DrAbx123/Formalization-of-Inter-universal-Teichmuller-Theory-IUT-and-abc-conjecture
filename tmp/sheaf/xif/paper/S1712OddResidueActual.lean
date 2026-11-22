import tmp.sheaf.xif.paper.S1711AdmissibleRealizationActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1711AdmissibleRealizationActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
local instance S1712GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
namespace LeanFormal.IUT.XiFPaper.S1712OddResidueActual
theorem S1712ConcreteFivePlace_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic concreteFivePlace = 5 := by
  have h := NumberFieldFinitePlace.residueCharacteristic_comap (k := ℚ)
    (K := GaussianField) concreteGaussianFivePlace
  rw [concreteGaussianFivePlace_comap,
    concreteGaussianFivePlace_residueCharacteristic] at h
  exact h
theorem S1712Odd : S1711OddResidueCharacteristic := by
  unfold S1711OddResidueCharacteristic
  have h := NumberFieldFinitePlace.residueCharacteristic_comap
    (k := ℚ) (K := S1687Field) S1687PlaceAboveFive
  rw [S1687PlaceAboveFive_comap] at h
  rw [← h, S1712ConcreteFivePlace_residueCharacteristic]
  norm_num
noncomputable def S1712RealizationData
    (hsplit : S1711RationalSplitAtFive) : S1687RealizationData :=
  S1711RealizationData S1712Odd hsplit
theorem S1712Admissible_of (hsplit : S1711RationalSplitAtFive) :
    S1667Admissible :=
  S1711Admissible_of S1712Odd hsplit
#check S1712Odd
#check S1712RealizationData
#check S1712Admissible_of
end LeanFormal.IUT.XiFPaper.S1712OddResidueActual
end

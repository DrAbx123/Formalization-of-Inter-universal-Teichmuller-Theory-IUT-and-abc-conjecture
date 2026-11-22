import tmp.sheaf.xif.paper.S1708NinePointInjectionActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1708NinePointInjectionActual
namespace LeanFormal.IUT.XiFPaper.S1711AdmissibleRealizationActual
def S1711OddResidueCharacteristic : Prop :=
  Odd (NumberFieldFinitePlace.residueCharacteristic S1687PlaceAboveFive)
def S1711RationalSplitAtFive : Prop := S1687RationalSplitAtFive
noncomputable def S1711RealizationData
    (hodd : S1711OddResidueCharacteristic)
    (hsplit : S1711RationalSplitAtFive) : S1687RealizationData where
  place := S1687PlaceAboveFive
  odd_residueCharacteristic := hodd
  torsion23 := S1708Torsion23Rational
  splitMultiplicative := S1687Split_of_rational hsplit
theorem S1711Admissible_of
    (hodd : S1711OddResidueCharacteristic)
    (hsplit : S1711RationalSplitAtFive) : S1667Admissible :=
  S1687Admissible_of_data (S1711RealizationData hodd hsplit)
#check S1711RealizationData
#check S1711Admissible_of
#check S1708Torsion23Rational
end LeanFormal.IUT.XiFPaper.S1711AdmissibleRealizationActual
end

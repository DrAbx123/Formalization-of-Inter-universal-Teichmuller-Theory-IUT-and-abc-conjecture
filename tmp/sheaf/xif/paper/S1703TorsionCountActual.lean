import tmp.sheaf.xif.paper.S1702AllTorsionRationalActual

/-! # S1703: torsion count/classification inputs

S1702 reduced the remaining Torsion23 inputs to geometric cardinalities
`Nat.card E[2] = 4` and `Nat.card E[3] = 9`.  This file records the stronger
explicit classifications that would give those cardinalities:

* 2-torsion: P = 0 or P = (x, 0) with Psi2(x) = 0;
* 3-torsion: P = 0 or P = (x, y) with Psi3(x) = 0.

No inhabitant is asserted.  No fake Nonempty, no arbitrary descent map. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1703TorsionCountActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1700ThreeTorsionExhaustionActual
open LeanFormal.IUT.XiFPaper.S1702AllTorsionRationalActual
open LeanFormal.IUT.XiFPaper.S1701Torsion23FullActual

local instance S1703ClosureDecEq : DecidableEq S1702Closure := Classical.decEq _
open WeierstrassCurve WeierstrassCurve.Affine

/-- Explicit 2-torsion classification over the algebraic closure. -/
def S1703TwoTorsionClassification : Prop :=
  ∀ P : S1702ClosurePoint, (2 : ℤ) • P = 0 →
    P = 0 ∨
      ∃ (x : S1702Closure) (hns : S1702CurveClosure.Nonsingular x 0),
        S1702CurveClosure.Ψ₂Sq.eval x = 0 ∧
          P = Affine.Point.some (W' := S1702CurveClosure) x 0 hns

/-- Explicit 3-torsion x-coordinate classification over the algebraic closure. -/
def S1703ThreeTorsionXClassification : Prop :=
  ∀ P : S1702ClosurePoint, (3 : ℤ) • P = 0 →
    P = 0 ∨
      ∃ (x y : S1702Closure) (hns : S1702CurveClosure.Nonsingular x y),
        S1702CurveClosure.Ψ₃.eval x = 0 ∧
          P = Affine.Point.some (W' := S1702CurveClosure) x y hns

/-- The exact first missing classification/count input: explicit 2-torsion
classification, explicit 3-torsion x classification, and the geometric
cardinalities. -/
def S1703FirstMissing : Prop :=
  S1703TwoTorsionClassification ∧
    S1703ThreeTorsionXClassification ∧
    S1702GeometricTwoTorsionCard ∧
    S1702GeometricThreeTorsionCard

/-- The already proved full Torsion23 conditional consumer from S1701/S1702. -/
theorem S1703Torsion23_of_parts
    (h2 : S1701Torsion2Rational) (h3 : S1701Torsion3Rational) :
    PuncturedEllipticCurve.Torsion23Rational
      (S1667Punctured.baseChange S1687Field) :=
  S1702Torsion23_of_parts h2 h3

#check S1703TwoTorsionClassification
#check S1703ThreeTorsionXClassification
#check S1703FirstMissing
#check S1703Torsion23_of_parts

end LeanFormal.IUT.XiFPaper.S1703TorsionCountActual
end

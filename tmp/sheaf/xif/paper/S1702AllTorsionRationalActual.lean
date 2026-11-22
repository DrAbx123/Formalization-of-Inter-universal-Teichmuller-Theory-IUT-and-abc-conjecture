import tmp.sheaf.xif.paper.S1701Torsion23FullActual

/-! # S1702: remaining AllNTorsionRational 2/3 inputs

S1701 reduced full `Torsion23Rational` to the two closure-descent statements
`S1701Torsion2Rational` and `S1701Torsion3Rational`.  This file records the
exact geometric cardinality inputs needed for the intended count argument:
over the algebraic closure, E[2] has 4 and E[3] has 9 points.  The F-rational
8 nonzero 3-torsion points are classified by S1700; adding 0 gives all 9
F-rational 3-torsion points.  The missing lemmas are the geometric cardinality
statements (`Nat.card` of the 2- and 3-torsion point types), not a fake
Nonempty or arbitrary descent map. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1702AllTorsionRationalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1700ThreeTorsionExhaustionActual
open LeanFormal.IUT.XiFPaper.S1701Torsion23FullActual
open WeierstrassCurve WeierstrassCurve.Affine

/-- The algebraic closure of the S1687 field. -/
abbrev S1702Closure : Type := AlgebraicClosure S1687Field

/-- The affine curve over the algebraic closure. -/
abbrev S1702CurveClosure : WeierstrassCurve.Affine S1702Closure :=
  (S1667Curve.baseChange S1687Field).baseChange S1702Closure |>.toAffine

local instance S1702ClosureDecEq : DecidableEq S1702Closure := Classical.decEq _

abbrev S1702ClosurePoint : Type :=
  WeierstrassCurve.Affine.Point (W' := S1702CurveClosure)

/-- Geometric 2-torsion cardinality: E[2] has 4 points. -/
def S1702GeometricTwoTorsionCard : Prop :=
  Nat.card { P : S1702ClosurePoint // (2 : ℤ) • P = 0 } = 4

/-- Geometric 3-torsion cardinality: E[3] has 9 points. -/
def S1702GeometricThreeTorsionCard : Prop :=
  Nat.card { P : S1702ClosurePoint // (3 : ℤ) • P = 0 } = 9

/-- The exact first missing count lemma for the 3-torsion descent. -/
def S1702ThreeTorsionCountMissing : Prop :=
  S1702GeometricThreeTorsionCard

/-- The exact first missing count lemma for the 2-torsion descent. -/
def S1702TwoTorsionCountMissing : Prop :=
  S1702GeometricTwoTorsionCard

/-- Full Torsion23Rational from the two S1701 closure-descent inputs. -/
theorem S1702Torsion23_of_parts
    (h2 : S1701Torsion2Rational) (h3 : S1701Torsion3Rational) :
    PuncturedEllipticCurve.Torsion23Rational
      (S1667Punctured.baseChange S1687Field) :=
  S1701Torsion23_of_parts h2 h3

/-- Exact missing package: the two closure-descent statements.  The intended
count argument needs S1702GeometricTwoTorsionCard and
S1702GeometricThreeTorsionCard. -/
def S1702FirstMissing : Prop :=
  S1701Torsion2Rational ∧ S1701Torsion3Rational

#check S1702GeometricTwoTorsionCard
#check S1702GeometricThreeTorsionCard
#check S1702TwoTorsionCountMissing
#check S1702ThreeTorsionCountMissing
#check S1702Torsion23_of_parts
#check S1702FirstMissing

end LeanFormal.IUT.XiFPaper.S1702AllTorsionRationalActual
end

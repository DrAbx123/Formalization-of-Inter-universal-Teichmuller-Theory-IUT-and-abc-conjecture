import tmp.sheaf.xif.paper.S1706FCardActual

/-! # S1707: F-rational 3-torsion cardinality - exact missing

S1706 proved `Nat.card E_F[2] = 4`.  The remaining input is
`Nat.card E_F[3] = 9`.  Nine candidate points are known: 0, the six S1687
root points, and the two rational points ±P.  What is not formalized here is
the simultaneous pairwise-distinctness lower bound (root points injective
from the six roots of H, rational points distinct and disjoint from root
points), together with the resulting `Nat.card` comparison. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1707ThreeTorsionFCardActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1704TorsionCardActual
open LeanFormal.IUT.XiFPaper.S1705AllTorsionRationalActual
open LeanFormal.IUT.XiFPaper.S1706FCardActual
open LeanFormal.IUT.XiFPaper.S1701Torsion23FullActual

/-- Exact missing lower-bound input: the nine explicit F-rational 3-torsion
points are pairwise distinct (equivalently the F-rational torsion subtype has
cardinality at least 9). -/
def S1707NinePointLowerBound : Prop :=
  9 ≤ Nat.card S1705FTorsion3

/-- Exact missing cardinality. -/
def S1707ThreeTorsionFCardMissing : Prop :=
  S1705ThreeTorsionFCard

/-- The actual S1706 conditional consumer. -/
theorem S1707Torsion23_of_threeCard
    (h3 : S1705ThreeTorsionFCard) :
    PuncturedEllipticCurve.Torsion23Rational
      (S1667Punctured.baseChange S1687Field) :=
  S1705Torsion23_of_FCards S1706TwoTorsionFCard h3

/-- The two-torsion half is already actual. -/
theorem S1707Torsion2Rational : S1701Torsion2Rational :=
  S1706Torsion2Rational

#check S1707NinePointLowerBound
#check S1707ThreeTorsionFCardMissing
#check S1707Torsion2Rational
#check S1707Torsion23_of_threeCard

end LeanFormal.IUT.XiFPaper.S1707ThreeTorsionFCardActual
end

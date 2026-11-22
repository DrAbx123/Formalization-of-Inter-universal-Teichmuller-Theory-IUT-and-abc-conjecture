import tmp.sheaf.xif.paper.S2935HeightLeProcessionActual
import tmp.sheaf.xif.paper.S2921HeightBridgeActual
import tmp.sheaf.xif.paper.S2923ThetaLinkBridgeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2935HeightLeProcessionActual
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2923ThetaLinkBridgeActual
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open Finset
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2936HeightBridgeAttemptActual

/-- Direction fact: collectionBound is antitone in Q when l > 0. -/
theorem S2936_collectionBound_antitone_Q
    {l D Q1 Q2 S T : Real} (hl : 0 < l) (hQ : Q1 <= Q2) (j : Nat) :
    collectionBound l D Q2 S T j <= collectionBound l D Q1 S T j := by
  unfold collectionBound
  have hcoef : 0 <= (j : Real) ^ 2 / (2 * l) := by positivity
  nlinarith

/-- The only actual Q comparison is a lower bound Q >= weight; it makes the
procession bound smaller, i.e. it goes in the wrong direction for an upper
bound on height. -/
theorem S2936_hweightvol_direction
    (n : Nat) (a b c : Nat) (habc : IsABCTriple a b c) (j : Nat) :
    collectionBound (2 * (n : Real) + 1) S2921D
        (S2921Q a b c) (S2921S a b c) (S2921T a b c) j <=
      collectionBound (2 * (n : Real) + 1) S2921D
        (arithmeticWeight (abcRationalPoint a c))
        (S2921S a b c) (S2921T a b c) j := by
  apply S2936_collectionBound_antitone_Q
  · positivity
  · exact S2921_hweightvol_candidate a b c habc

/-- The actual J-height comparison is a lower bound, not an upper bound. -/
theorem S2936_height_lower_bound
    (a b c : Nat) (habc : IsABCTriple a b c) :
    6 * Height.logHeight₁ (abcRationalPoint a c) + Real.log (27 / 64 : Real) <=
      Height.logHeight₁ (abcJInvariant a b c) :=
  S2838_height_le_Jlog a b c habc

/-- The exact target remains the missing analytic bridge. -/
def S2936HeightBridgeTarget (n : Nat) : Prop :=
  S2935HeightLeProcession n

#check S2936_collectionBound_antitone_Q
#check S2936_hweightvol_direction
#check S2936_height_lower_bound
#check S2936HeightBridgeTarget
#print axioms S2936_collectionBound_antitone_Q
#print axioms S2936_hweightvol_direction
#print axioms S2936_height_lower_bound

end LeanFormal.IUT.XiFPaper.S2936HeightBridgeAttemptActual
end

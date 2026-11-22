import tmp.sheaf.xif.paper.S2068PsiCnsActorReduction
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2068PsiCnsActorReduction
namespace LeanFormal.IUT.XiFPaper.S2069GroupAlgorithmGap
/-- Exact missing data for the group algorithm of IUT II Example 1.8(iii)-(iv):
a functorial assignment, for every profinite group G, of the group-theoretic
O-times-mu(G) built from G alone.  No construction is asserted. -/
structure S2069GroupAlgorithmReconstruction where
  units : ProfiniteGrp → Type
  [commMonoidUnits : ∀ G : ProfiniteGrp, CommMonoid (units G)]
  map : ∀ {G H : ProfiniteGrp}, G ≃* H → units G ≃* units H
/-- The exact missing reconstruction supplies S2068GroupAlgorithm. -/
noncomputable def S2069GroupAlgorithmOfReconstruction
    (R : S2069GroupAlgorithmReconstruction) : S2068GroupAlgorithm where
  alg := R.units
  commMonoidAlg := R.commMonoidUnits
  algMap := R.map
/-- Exact first missing for (c): an inhabitant of this type, i.e. the
actual group-theoretic algorithm of Example 1.8(iii)-(iv). -/
abbrev S2069GroupAlgorithmRequired : Type 1 := S2069GroupAlgorithmReconstruction
#check S2069GroupAlgorithmReconstruction
#check S2069GroupAlgorithmOfReconstruction
#check S2069GroupAlgorithmRequired
end LeanFormal.IUT.XiFPaper.S2069GroupAlgorithmGap
end

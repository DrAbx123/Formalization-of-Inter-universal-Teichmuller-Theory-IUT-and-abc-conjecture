import tmp.sheaf.xif.paper.S2384H1ComparisonActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open KummerTheory
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2360KummerH1Actual
open LeanFormal.IUT.XiFPaper.S2384H1ComparisonActual
namespace LeanFormal.IUT.XiFPaper.S2390H1ComparisonDoneActual
variable (p : Nat) [Fact (Nat.Prime p)] (n : ℕ)
local instance s2390MulDistrib :
    MulDistribMulAction (LocalAbsoluteGalois p) (S2145Coeff p n) :=
  MulDistribMulAction.compHom (S2145Coeff p n)
    ((S2196MuActionTower p).actn n).automorphism
/-- Internal continuous 1-cocycles map to external continuous 1-cocycles by
the identity on the underlying function; commutativity converts the cocycle
law. -/
noncomputable def S2390ToExternalCocycle
    (z : Iut.ContinuousOneCocycle
      ((S2196MuActionTower p).actn n)) :
    ContH1.cocycles (LocalAbsoluteGalois p) (S2145Coeff p n) where
  val := z.toFun
  property := by
    refine ⟨z.continuous_toFun, ?_⟩
    intro g h
    rw [z.map_mul']
    change z.toFun g *
        ((S2196MuActionTower p).actn n).act g (z.toFun h) =
      ((S2196MuActionTower p).actn n).act g (z.toFun h) * z.toFun g
    exact mul_comm _ _
/-- External continuous 1-cocycles map back to internal continuous 1-cocycles. -/
noncomputable def S2390OfExternalCocycle
    (z : ContH1.cocycles (LocalAbsoluteGalois p) (S2145Coeff p n)) :
    Iut.ContinuousOneCocycle
      ((S2196MuActionTower p).actn n) where
  toFun := z.1
  continuous_toFun := z.2.1
  map_mul' g h := by
    have hc := z.2.2 g h
    rw [hc]
    change ((S2196MuActionTower p).actn n).act g (z.1 h) * z.1 g =
      z.1 g * ((S2196MuActionTower p).actn n).act g (z.1 h)
    exact mul_comm _ _
theorem S2390OfTo (z : Iut.ContinuousOneCocycle
      ((S2196MuActionTower p).actn n)) :
    S2390OfExternalCocycle p n (S2390ToExternalCocycle p n z) = z := by
  apply Iut.ContinuousOneCocycle.ext
  intro g
  rfl
theorem S2390ToOf (z : ContH1.cocycles (LocalAbsoluteGalois p) (S2145Coeff p n)) :
    S2390ToExternalCocycle p n (S2390OfExternalCocycle p n z) = z := by
  apply Subtype.ext
  rfl
/-- Exact first missing: the quotient-level comparison. -/
structure S2390H1ComparisonRequired where
  equiv : S2204H1 p n ≃ ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n)
#check S2390ToExternalCocycle
#check S2390OfExternalCocycle
#check S2390OfTo
#check S2390ToOf
#check S2390H1ComparisonRequired
end LeanFormal.IUT.XiFPaper.S2390H1ComparisonDoneActual
end

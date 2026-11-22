import tmp.sheaf.xif.paper.S2204ActualH1InstanceActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2164MuActionTowerActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
namespace LeanFormal.IUT.XiFPaper.S2210H1FiniteActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- Pointwise coefficient pushforward on continuous 1-cochains, from level
n+1 to level n, along the actual power map. -/
noncomputable def S2210CochainPushforward (n : ℕ)
    (z : Iut.ContinuousOneCocycle ((S2196MuActionTower p).actn (n+1))) :
    Iut.ContinuousOneCocycle ((S2196MuActionTower p).actn n) where
  toFun g := S2145PowMap p n (z g)
  continuous_toFun := continuous_of_discreteTopology.comp z.continuous_toFun
  map_mul' g h := by
    change S2145PowMap p n (z (g * h)) =
      S2145PowMap p n (z g) *
        ((S2196MuActionTower p).actn n).act g (S2145PowMap p n (z h))
    rw [z.map_mul', map_mul]
    have h1 : ((S2196MuActionTower p).actn (n+1)).act g (z h) =
        S2164RootsActionAut p (n+1) g (z h) := rfl
    have h0 : ((S2196MuActionTower p).actn n).act g (S2145PowMap p n (z h)) =
        S2164RootsActionAut p n g (S2145PowMap p n (z h)) := rfl
    rw [h1, h0, S2164PowMap_equivariant p n g (z h)]
/-- The pushforward is a monoid homomorphism of continuous 1-cocycle groups. -/
noncomputable def S2210CocyclePushforwardHom (n : ℕ) :
    Iut.ContinuousOneCocycle ((S2196MuActionTower p).actn (n+1)) →*
      Iut.ContinuousOneCocycle ((S2196MuActionTower p).actn n) where
  toFun := S2210CochainPushforward p n
  map_one' := by
    apply Iut.ContinuousOneCocycle.ext
    intro g
    simp [S2210CochainPushforward]
  map_mul' z w := by
    apply Iut.ContinuousOneCocycle.ext
    intro g
    simp [S2210CochainPushforward, map_mul]
/-- Exact first missing: the induced map on H^1 classes. -/
def S2210H1PushforwardRequired (n : ℕ) : Type :=
  S2204H1 p (n+1) →* S2204H1 p n
/-- Exact first missing: finiteness of the H^1 levels. -/
def S2210H1FiniteRequired : Prop :=
  ∀ n, Finite (S2204H1 p n)
#check S2210CochainPushforward
#check S2210CocyclePushforwardHom
#check S2210H1PushforwardRequired
#check S2210H1FiniteRequired
end LeanFormal.IUT.XiFPaper.S2210H1FiniteActual
end

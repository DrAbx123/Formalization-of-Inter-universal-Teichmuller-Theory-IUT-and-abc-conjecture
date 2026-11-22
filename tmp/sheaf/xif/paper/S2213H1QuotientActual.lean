import tmp.sheaf.xif.paper.S2210H1FiniteActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2164MuActionTowerActual
open LeanFormal.IUT.XiFPaper.S2210H1FiniteActual
namespace LeanFormal.IUT.XiFPaper.S2213H1QuotientActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The cocycle pushforward respects coboundary equivalence. -/
theorem S2213Pushforward_cohomologous (n : ℕ)
    {z w : Iut.ContinuousOneCocycle ((S2196MuActionTower p).actn (n+1))}
    (h : z.Cohomologous w) :
    (S2210CochainPushforward p n z).Cohomologous
      (S2210CochainPushforward p n w) := by
  rcases h with ⟨a, rfl⟩
  refine ⟨S2145PowMap p n a, ?_⟩
  apply Iut.ContinuousOneCocycle.ext
  intro g
  change S2145PowMap p n
      (a⁻¹ * z g * ((S2196MuActionTower p).actn (n+1)).act g a) =
    (S2145PowMap p n a)⁻¹ * S2145PowMap p n (z g) *
      ((S2196MuActionTower p).actn n).act g (S2145PowMap p n a)
  rw [map_mul, map_mul, map_inv]
  have h1 : ((S2196MuActionTower p).actn (n+1)).act g a =
      S2164RootsActionAut p (n+1) g a := rfl
  have h0 : ((S2196MuActionTower p).actn n).act g (S2145PowMap p n a) =
      S2164RootsActionAut p n g (S2145PowMap p n a) := rfl
  rw [h1, h0, S2164PowMap_equivariant p n g a]
/-- The induced map on continuous H^1. -/
noncomputable def S2213H1Pushforward (n : ℕ) :
    S2204H1 p (n+1) → S2204H1 p n :=
  Quotient.map (S2210CochainPushforward p n)
    (fun _ _ h => S2213Pushforward_cohomologous p n h)
/-- Exact missing: the induced quotient map as a monoid homomorphism. -/
abbrev S2213H1PushforwardMonoidRequired (n : ℕ) : Type :=
  S2204H1 p (n+1) →* S2204H1 p n
#check S2213Pushforward_cohomologous
#check S2213H1Pushforward
#check S2213H1PushforwardMonoidRequired
end LeanFormal.IUT.XiFPaper.S2213H1QuotientActual
end

import tmp.sheaf.xif.paper.S2214H1MonoidActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
namespace LeanFormal.IUT.XiFPaper.S2220H1FiniteSurjActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- A finite quotient through which the G_v-action on mu_{n!} factors. -/
structure S2220FiniteQuotientAction (n : ℕ) where
  Q : Type
  [groupQ : Group Q]
  [finiteQ : Finite Q]
  q : LocalAbsoluteGalois p →* Q
  q_surjective : Function.Surjective q
  actionQ : Q →* MulAut (S2145Coeff p n)
  compat : ∀ g, actionQ (q g) =
    ((S2196MuActionTower p).actn n).automorphism g
/-- Exact missing: finiteness of the actual level H^1. -/
def S2220H1FiniteRequired : Prop :=
  ∀ n, Finite (S2204H1 p n)
/-- Exact missing: surjectivity of the power-induced H^1 transition. -/
def S2220H1SurjectiveRequired : Prop :=
  ∀ n, Function.Surjective (⇑(S2214H1PushforwardHom p n))
#check S2220FiniteQuotientAction
#check S2220H1FiniteRequired
#check S2220H1SurjectiveRequired
end LeanFormal.IUT.XiFPaper.S2220H1FiniteSurjActual
end

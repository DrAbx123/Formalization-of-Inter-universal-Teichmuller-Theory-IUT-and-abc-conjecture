import tmp.sheaf.xif.paper.S2196ActionContinuousProofActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
namespace LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The actual level H^1 carrier of the mu_{n!} tower. -/
abbrev S2204H1 (n : ℕ) : Type :=
  Iut.ContinuousH1 ((S2196MuActionTower p).actn n)
/-- The remaining H^1 data: finiteness, the power-induced transition, and
its surjectivity.  This is exactly the gap between the actual action tower
and S2145ActualMuH1Instance. -/
structure S2204H1InstanceData where
  finiteH1 : ∀ n, Finite (S2204H1 p n)
  proj : ∀ n, S2204H1 p (n+1) →* S2204H1 p n
  proj_surjective : ∀ n, Function.Surjective (proj n)
/-- Given the H^1 data, the actual S2145 instance is produced from the actual
action tower S2196MuActionTower. -/
noncomputable def S2204ToS2145Instance
    (A : S2204H1InstanceData p) :
    S2145ActualMuH1Instance p where
  actn := (S2196MuActionTower p).actn
  compat := (S2196MuActionTower p).compat
  finiteH1 := A.finiteH1
  proj := A.proj
  proj_surjective := A.proj_surjective
/-- Exact first missing: the H^1 finiteness. -/
def S2204H1FiniteRequired : Prop :=
  ∀ n, Finite (S2204H1 p n)
/-- Exact first missing: the power-induced transition map. -/
abbrev S2204H1ProjRequired (n : ℕ) : Type :=
  S2204H1 p (n+1) →* S2204H1 p n
/-- Exact first missing: surjectivity of that transition. -/
def S2204H1ProjSurjectiveRequired
    (proj : ∀ n, S2204H1ProjRequired p n) : Prop :=
  ∀ n, Function.Surjective (⇑(proj n))
#check S2204H1
#check S2204H1InstanceData
#check S2204ToS2145Instance
#check S2204H1FiniteRequired
#check S2204H1ProjRequired
#check S2204H1ProjSurjectiveRequired
end LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
end

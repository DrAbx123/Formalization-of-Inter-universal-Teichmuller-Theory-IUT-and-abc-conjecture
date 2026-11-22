import tmp.sheaf.xif.paper.S2410H1EquivDoneActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
open LeanFormal.IUT.XiFPaper.S2410H1EquivDoneActual
namespace LeanFormal.IUT.XiFPaper.S2420H1InstanceFiniteActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The remaining S2214 H^1 data, with the finiteness field now actual and
only surjectivity assumed. -/
noncomputable def S2420H1RemainingDataOfSurjective
    (hsurj : ∀ n, Function.Surjective
      (⇑(S2214H1PushforwardHom p n))) :
    S2214H1RemainingData p where
  finiteH1 := fun n => S2410FiniteH1 p n
  proj_surjective := hsurj
/-- The actual S2145 H^1 instance from S2196 and H^1 surjectivity. -/
noncomputable def S2420ToS2145Instance
    (hsurj : ∀ n, Function.Surjective
      (⇑(S2214H1PushforwardHom p n))) :
    S2145ActualMuH1Instance p :=
  S2214ToS2145Instance p
    (S2420H1RemainingDataOfSurjective p hsurj)
#check S2420H1RemainingDataOfSurjective
#check S2420ToS2145Instance
end LeanFormal.IUT.XiFPaper.S2420H1InstanceFiniteActual
end

import tmp.sheaf.xif.paper.S2213H1QuotientActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2210H1FiniteActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2213H1QuotientActual
namespace LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The quotient pushforward as a monoid homomorphism. -/
noncomputable def S2214H1PushforwardHom (n : ℕ) :
    S2204H1 p (n+1) →* S2204H1 p n where
  toFun := S2213H1Pushforward p n
  map_one' := by
    change Quotient.mk _ ((S2210CocyclePushforwardHom p n) 1) =
      Quotient.mk _ (1 : Iut.ContinuousOneCocycle ((S2196MuActionTower p).actn n))
    rw [(S2210CocyclePushforwardHom p n).map_one]
  map_mul' z w := by
    refine Quotient.inductionOn₂ z w ?_
    intro z w
    change Quotient.mk _ ((S2210CocyclePushforwardHom p n) (z * w)) =
      Quotient.mk _ ((S2210CocyclePushforwardHom p n) z *
        (S2210CocyclePushforwardHom p n) w)
    rw [(S2210CocyclePushforwardHom p n).map_mul]
/-- The remaining H^1 finiteness and transition-surjectivity data. -/
structure S2214H1RemainingData where
  finiteH1 : ∀ n, Finite (S2204H1 p n)
  proj_surjective : ∀ n, Function.Surjective
    (⇑(S2214H1PushforwardHom p n))
/-- With the remaining data, the actual S2204 H^1 instance is obtained. -/
noncomputable def S2214ToS2204H1InstanceData
    (A : S2214H1RemainingData p) : S2204H1InstanceData p where
  finiteH1 := A.finiteH1
  proj := fun n => S2214H1PushforwardHom p n
  proj_surjective := A.proj_surjective
noncomputable def S2214ToS2145Instance
    (A : S2214H1RemainingData p) : S2145ActualMuH1Instance p :=
  S2204ToS2145Instance p (S2214ToS2204H1InstanceData p A)
#check S2214H1PushforwardHom
#check S2214H1RemainingData
#check S2214ToS2204H1InstanceData
#check S2214ToS2145Instance
end LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
end

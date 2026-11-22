import tmp.sheaf.xif.paper.S2425H1SurjInternal
import tmp.sheaf.xif.paper.S2426H1Lim1Actual
import tmp.sheaf.xif.paper.S2420H1InstanceFiniteActual
import tmp.sheaf.xif.paper.S2422H1MLInstanceActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2138H1MLActual
open LeanFormal.IUT.XiFPaper.S2142ActualH1TowerActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
open LeanFormal.IUT.XiFPaper.S2410H1EquivDoneActual
open LeanFormal.IUT.XiFPaper.S2425H1SurjInternal
open LeanFormal.IUT.XiFPaper.S2426H1Lim1Actual
namespace LeanFormal.IUT.XiFPaper.S2430H1FinalActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The actual transition-surjectivity input of S2426, now inhabited by S2425. -/
noncomputable def S2430ActualH1TransitionSurjective :
    S2426ActualH1TransitionSurjective p :=
  ⟨S2425H1Surjective p⟩
/-- The actual S2145 H^1 instance, with no remaining hypotheses. -/
noncomputable def S2430ActualS2145Instance : S2145ActualMuH1Instance p :=
  S2426ActualS2145Instance p (S2430ActualH1TransitionSurjective p)
/-- The actual S2142 tower. -/
noncomputable def S2430ActualS2142Tower : S2142ActualMuH1Tower where
  p := p
  hprime := inferInstance
  coeff := S2145Coeff p
  actn := (S2196MuActionTower p).actn
  finiteH1 := fun n => S2410FiniteH1 p n
  proj := fun n => S2214H1PushforwardHom p n
  proj_surjective := S2425H1Surjective p
/-- Mittag-Leffler for the actual H^1 tower, unconditional. -/
theorem S2430ActualMittagLeffler :
    S2138MittagLeffler
      (S2142ToS2138Tower (S2430ActualS2142Tower p)) :=
  S2142MittagLeffler (S2430ActualS2142Tower p)
/-- lim¹ H¹ = 0 for the actual H^1 tower, unconditional. -/
theorem S2430ActualH1Lim1_subsingleton :
    Subsingleton (S2426Lim1 (S2426ActualH1Tower p)) :=
  S2426ActualH1Lim1_subsingleton p
    (S2430ActualH1TransitionSurjective p)
#check S2430ActualH1TransitionSurjective
#check S2430ActualS2145Instance
#check S2430ActualS2142Tower
#check S2430ActualMittagLeffler
#check S2430ActualH1Lim1_subsingleton
end LeanFormal.IUT.XiFPaper.S2430H1FinalActual
end

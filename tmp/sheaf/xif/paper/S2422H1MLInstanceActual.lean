import tmp.sheaf.xif.paper.S2420H1InstanceFiniteActual
import tmp.sheaf.xif.paper.S2138H1MLActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2138H1MLActual
open LeanFormal.IUT.XiFPaper.S2145MuH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2196ActionContinuousProofActual
open LeanFormal.IUT.XiFPaper.S2204ActualH1InstanceActual
open LeanFormal.IUT.XiFPaper.S2214H1MonoidActual
open LeanFormal.IUT.XiFPaper.S2410H1EquivDoneActual
open LeanFormal.IUT.XiFPaper.S2420H1InstanceFiniteActual
namespace LeanFormal.IUT.XiFPaper.S2422H1MLInstanceActual
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The actual S2138 H^1 tower, with finiteness from S2410 and surjective
transitions as an explicit hypothesis. -/
noncomputable def S2422ActualTowerOfSurjective
    (hsurj : ∀ n, Function.Surjective
      (⇑(S2214H1PushforwardHom p n))) :
    S2138ActualMuH1Tower where
  H1 := S2204H1 p
  finite := fun n => S2410FiniteH1 p n
  proj := fun n => S2214H1PushforwardHom p n
  proj_surjective := hsurj
/-- Mittag-Leffler for the actual H^1 tower from surjective transitions. -/
theorem S2422MittagLefflerOfSurjective
    (hsurj : ∀ n, Function.Surjective
      (⇑(S2214H1PushforwardHom p n))) :
    S2138MittagLeffler
      (S2422ActualTowerOfSurjective p hsurj).toS2138H1Tower :=
  S2138ActualMuH1Tower_mittagLeffler
    (S2422ActualTowerOfSurjective p hsurj)
#check S2422ActualTowerOfSurjective
#check S2422MittagLefflerOfSurjective
end LeanFormal.IUT.XiFPaper.S2422H1MLInstanceActual
end

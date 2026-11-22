import tmp.sheaf.xif.paper.S3076QPrimeMapCompActual
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
namespace LeanFormal.IUT.XiFPaper.S3076TorsorIsoCommProbe
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

theorem S3076CompComm :
    S3076CompToB f g P ≫
      (S3073PullbackFiber g (S3073PullbackFiber f P)).projection =
    (S3073PullbackFiber (f ≫ g) P).projection := by
  change pullback.lift (S3076CompToC f g P)
      (pullback.snd (f := S3076CompE P) (g := (S3076CompG g) ≫ (S3076CompF f))) _ ≫
      pullback.snd (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
        (g := S3076CompG g) =
    pullback.snd (f := S3076CompE P) (g := (S3076CompG g) ≫ (S3076CompF f))
  rw [pullback.lift_snd]

#check S3076CompComm
end LeanFormal.IUT.XiFPaper.S3076TorsorIsoCommProbe
end

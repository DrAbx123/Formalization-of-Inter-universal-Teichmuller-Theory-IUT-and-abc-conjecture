import tmp.sheaf.xif.paper.S3076TorsorIsoCommProbe
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
namespace LeanFormal.IUT.XiFPaper.S3076TorsorIsoEquivProbeAdapted
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

/-- Conditional equivariance, with the ToC action compatibility as an explicit
hypothesis (to be supplied by multiradial). -/
theorem S3076CompEquivariant
    (hC : ∀ h : SignGroup,
      S3076CompUnitProbe.S3076CompToC f g P ≫ (S3073PullbackFiber f P).action h =
        (S3073PullbackFiber (f ≫ g) P).action h ≫ S3076CompUnitProbe.S3076CompToC f g P)
    (h : SignGroup) :
    S3076CompUnitProbe.S3076CompToB f g P ≫
      (S3073PullbackFiber g (S3073PullbackFiber f P)).action h =
    (S3073PullbackFiber (f ≫ g) P).action h ≫ S3076CompUnitProbe.S3076CompToB f g P := by
  apply pullback.hom_ext
    (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
    (g := S3076CompG g)
  · rw [Category.assoc]
    change S3076CompUnitProbe.S3076CompToB f g P ≫
      (S3073PullbackAction g (S3073PullbackFiber f P) h ≫
        pullback.fst (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
          (g := S3076CompG g)) =
      (S3073PullbackAction (f ≫ g) P h ≫ S3076CompUnitProbe.S3076CompToB f g P) ≫
        pullback.fst (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
          (g := S3076CompG g)
    rw [pullback.lift_fst]
    rw [← Category.assoc]
    unfold S3076CompUnitProbe.S3076CompToB
    rw [pullback.lift_fst]
    rw [hC h]
    rw [Category.assoc]
    unfold S3076CompUnitProbe.S3076CompToB
    rw [pullback.lift_fst]
  · rw [Category.assoc]
    change S3076CompUnitProbe.S3076CompToB f g P ≫
      (S3073PullbackAction g (S3073PullbackFiber f P) h ≫
        pullback.snd (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
          (g := S3076CompG g)) =
      (S3073PullbackAction (f ≫ g) P h ≫ S3076CompUnitProbe.S3076CompToB f g P) ≫
        pullback.snd (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
          (g := S3076CompG g)
    rw [pullback.lift_snd]
    unfold S3076CompUnitProbe.S3076CompToB
    rw [pullback.lift_snd]
    rw [Category.assoc]
    rw [pullback.lift_snd]
    unfold S3076CompUnitProbe.S3076CompToB
    rw [pullback.lift_snd]

#check S3076CompEquivariant
end LeanFormal.IUT.XiFPaper.S3076TorsorIsoEquivProbeAdapted
end

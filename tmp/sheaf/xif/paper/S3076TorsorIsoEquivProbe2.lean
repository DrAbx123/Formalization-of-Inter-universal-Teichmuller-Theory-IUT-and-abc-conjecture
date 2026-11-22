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
namespace LeanFormal.IUT.XiFPaper.S3076TorsorIsoEquivProbe2
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

noncomputable def S3076CompToB' :
    S3073PullbackTotal (f ≫ g) P ⟶
      S3073PullbackTotal g (S3073PullbackFiber f P) :=
  S3076CompUnitProbe.S3076CompToB f g P

noncomputable def S3076CompToC' :
    S3073PullbackTotal (f ≫ g) P ⟶ S3073PullbackTotal f P :=
  S3076CompUnitProbe.S3076CompToC f g P

theorem S3076CompEquivariant'
    (hC : ∀ h : SignGroup,
      S3076CompToC' f g P ≫ S3073PullbackAction f P h =
        S3073PullbackAction (f ≫ g) P h ≫ S3076CompToC' f g P)
    (h : SignGroup) :
    S3076CompToB' f g P ≫
      S3073PullbackAction g (S3073PullbackFiber f P) h =
    S3073PullbackAction (f ≫ g) P h ≫ S3076CompToB' f g P := by
  apply pullback.hom_ext
    (f := pullback.snd (f := S3076CompE P) (g := S3076CompF f))
    (g := S3076CompG g)
  · rw [Category.assoc]
    unfold S3073PullbackAction
    rw [pullback.lift_fst]
    rw [← Category.assoc]
    simp only [S3076CompToB', S3076CompToB]
    rw [pullback.lift_fst]
    rw [hC h]
    rw [Category.assoc]
    simp only [S3076CompToB', S3076CompToB]
    rw [pullback.lift_fst]
  · rw [Category.assoc]
    unfold S3073PullbackAction
    rw [pullback.lift_snd]
    simp only [S3076CompToB', S3076CompToB]
    rw [pullback.lift_snd]
    rw [Category.assoc]
    rw [show S3073PullbackAction (f ≫ g) P h ≫
        pullback.snd (f := S3076CompE P) (g := (S3076CompG g) ≫ (S3076CompF f)) =
        pullback.snd (f := S3076CompE P) (g := (S3076CompG g) ≫ (S3076CompF f))
        from pullback.lift_snd]
    simp only [S3076CompToB', S3076CompToB]
    rw [pullback.lift_snd]

#check S3076CompToB'
#check S3076CompToC'
#check S3076CompEquivariant'
end LeanFormal.IUT.XiFPaper.S3076TorsorIsoEquivProbe2
end

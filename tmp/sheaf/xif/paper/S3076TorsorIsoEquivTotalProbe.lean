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
namespace LeanFormal.IUT.XiFPaper.S3076TorsorIsoEquivTotalProbe
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

abbrev S3076A : Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  S3073PullbackTotal (f ≫ g) P
abbrev S3076C : Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  S3073PullbackTotal f P
abbrev S3076B : Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  S3073PullbackTotal g (S3073PullbackFiber f P)

noncomputable def S3076ToC' : S3076A f g P ⟶ S3076C f P :=
  pullback.lift
    (pullback.fst (f := S3076CompE P)
      (g := (S3076CompG g) ≫ (S3076CompF f)))
    (pullback.snd (f := S3076CompE P)
      (g := (S3076CompG g) ≫ (S3076CompF f)) ≫ S3076CompG g)
    (by
      rw [Category.assoc]
      exact pullback.condition)

noncomputable def S3076ToB' : S3076A f g P ⟶ S3076B f g P :=
  pullback.lift
    (S3076ToC' f g P)
    (pullback.snd (f := S3076CompE P)
      (g := (S3076CompG g) ≫ (S3076CompF f)))
    (by
      show S3076ToC' f g P ≫
          pullback.snd (f := S3076CompE P) (g := S3076CompF f) =
        pullback.snd (f := S3076CompE P)
          (g := (S3076CompG g) ≫ (S3076CompF f)) ≫ S3076CompG g
      rw [S3076ToC', pullback.lift_snd])

theorem S3076ToC'_action (h : SignGroup) :
    S3076ToC' f g P ≫ S3073PullbackAction f P h =
      S3073PullbackAction (f ≫ g) P h ≫ S3076ToC' f g P := by
  apply pullback.hom_ext (f := S3076CompE P) (g := S3076CompF f)
  · rw [Category.assoc]
    simp only [S3076ToC', S3073PullbackAction]
    rw [pullback.lift_fst]
    rw [Category.assoc]
    rw [pullback.lift_fst]
  · rw [Category.assoc]
    simp only [S3076ToC', S3073PullbackAction]
    rw [pullback.lift_snd]
    rw [Category.assoc]
    rw [pullback.lift_snd]

theorem S3076EquivTotal (h : SignGroup) :
    S3076ToB' f g P ≫ S3073PullbackAction g (S3073PullbackFiber f P) h =
      S3073PullbackAction (f ≫ g) P h ≫ S3076ToB' f g P := by
  apply pullback.hom_ext
    (f := S3073PullbackProjection f P) (g := S3076CompG g)
  · rw [Category.assoc]
    simp only [S3076ToB', S3073PullbackAction]
    rw [pullback.lift_fst]
    rw [Category.assoc]
    rw [S3076ToC'_action]
    rw [Category.assoc]
  · rw [Category.assoc]
    simp only [S3076ToB', S3073PullbackAction]
    rw [pullback.lift_snd]
    rw [Category.assoc]
    rw [pullback.lift_snd]

#check S3076ToC'
#check S3076ToB'
#check S3076ToC'_action
#check S3076EquivTotal
end LeanFormal.IUT.XiFPaper.S3076TorsorIsoEquivTotalProbe
end

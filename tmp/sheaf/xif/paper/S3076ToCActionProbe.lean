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
namespace LeanFormal.IUT.XiFPaper.S3076ToCActionProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

abbrev S3076A : Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  S3073PullbackTotal (f ≫ g) P
abbrev S3076C : Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  S3073PullbackTotal f P

noncomputable def S3076ToC' : S3076A f g P ⟶ S3076C f P :=
  pullback.lift
    (pullback.fst (f := S3076CompE P)
      (g := (S3076CompG g) ≫ (S3076CompF f)))
    (pullback.snd (f := S3076CompE P)
      (g := (S3076CompG g) ≫ (S3076CompF f)) ≫ S3076CompG g)
    (by
      rw [Category.assoc]
      exact pullback.condition)

theorem S3076Action_fst
    {X Y : LocallyDiscrete Cᵒᵖ} (F' : X ⟶ Y)
    (Q : S3048SignTorsorFiber X) (h : SignGroup) :
    S3073PullbackAction F' Q h ≫
      pullback.fst (f := Q.projection) (g := F'.as.unop) =
    pullback.fst (f := Q.projection) (g := F'.as.unop) ≫ Q.action h := by
  unfold S3073PullbackAction
  rw [pullback.lift_fst]

theorem S3076Action_snd
    {X Y : LocallyDiscrete Cᵒᵖ} (F' : X ⟶ Y)
    (Q : S3048SignTorsorFiber X) (h : SignGroup) :
    S3073PullbackAction F' Q h ≫
      pullback.snd (f := Q.projection) (g := F'.as.unop) =
    pullback.snd (f := Q.projection) (g := F'.as.unop) := by
  unfold S3073PullbackAction
  rw [pullback.lift_snd]

theorem S3076ToC_action (h : SignGroup) :
    S3076ToC' f g P ≫ S3073PullbackAction f P h =
      S3073PullbackAction (f ≫ g) P h ≫ S3076ToC' f g P := by
  apply pullback.hom_ext (f := S3076CompE P) (g := S3076CompF f)
  · calc
      (S3076ToC' f g P ≫ S3073PullbackAction f P h) ≫
          pullback.fst (f := S3076CompE P) (g := S3076CompF f)
          = S3076ToC' f g P ≫
            (S3073PullbackAction f P h ≫
              pullback.fst (f := S3076CompE P) (g := S3076CompF f)) := by
                rw [Category.assoc]
      _ = S3076ToC' f g P ≫
            (pullback.fst (f := S3076CompE P) (g := S3076CompF f) ≫
              P.action h) := by rw [S3076Action_fst]
      _ = (S3076ToC' f g P ≫
            pullback.fst (f := S3076CompE P) (g := S3076CompF f)) ≫
            P.action h := by rw [Category.assoc]
      _ = pullback.fst (f := S3076CompE P)
            (g := (S3076CompG g) ≫ (S3076CompF f)) ≫ P.action h := by
              rw [S3076ToC', pullback.lift_fst]
      _ = S3073PullbackAction (f ≫ g) P h ≫
            pullback.fst (f := S3076CompE P)
              (g := (S3076CompG g) ≫ (S3076CompF f)) := by
              change pullback.fst (f := P.projection) (g := (f ≫ g).as.unop) ≫ P.action h =
                S3073PullbackAction (f ≫ g) P h ≫
                  pullback.fst (f := P.projection) (g := (f ≫ g).as.unop)
              rw [← S3076Action_fst]
      _ = S3073PullbackAction (f ≫ g) P h ≫
            (S3076ToC' f g P ≫
              pullback.fst (f := S3076CompE P) (g := S3076CompF f)) := by
              rw [S3076ToC', pullback.lift_fst]
      _ = (S3073PullbackAction (f ≫ g) P h ≫ S3076ToC' f g P) ≫
            pullback.fst (f := S3076CompE P) (g := S3076CompF f) := by
              rw [Category.assoc]
  · calc
      (S3076ToC' f g P ≫ S3073PullbackAction f P h) ≫
          pullback.snd (f := S3076CompE P) (g := S3076CompF f)
          = S3076ToC' f g P ≫
            (S3073PullbackAction f P h ≫
              pullback.snd (f := S3076CompE P) (g := S3076CompF f)) := by
                rw [Category.assoc]
      _ = S3076ToC' f g P ≫
            pullback.snd (f := S3076CompE P) (g := S3076CompF f) := by
              rw [S3076Action_snd]
      _ = pullback.snd (f := S3076CompE P)
            (g := (S3076CompG g) ≫ (S3076CompF f)) ≫ S3076CompG g := by
              rw [S3076ToC', pullback.lift_snd]
      _ = S3073PullbackAction (f ≫ g) P h ≫
            (pullback.snd (f := S3076CompE P)
              (g := (S3076CompG g) ≫ (S3076CompF f)) ≫ S3076CompG g) := by
              change pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫ S3076CompG g =
                S3073PullbackAction (f ≫ g) P h ≫
                  (pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫ S3076CompG g)
              rw [← Category.assoc, S3076Action_snd]
      _ = S3073PullbackAction (f ≫ g) P h ≫
            (S3076ToC' f g P ≫
              pullback.snd (f := S3076CompE P) (g := S3076CompF f)) := by
              rw [S3076ToC', pullback.lift_snd]
      _ = (S3073PullbackAction (f ≫ g) P h ≫ S3076ToC' f g P) ≫
            pullback.snd (f := S3076CompE P) (g := S3076CompF f) := by
              rw [Category.assoc]

#check S3076ToC_action
#check S3076Action_fst
#check S3076Action_snd
end LeanFormal.IUT.XiFPaper.S3076ToCActionProbe
end

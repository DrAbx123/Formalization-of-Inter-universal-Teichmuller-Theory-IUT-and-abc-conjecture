import tmp.sheaf.xif.paper.S3076ToCActionProbe
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
namespace LeanFormal.IUT.XiFPaper.S3076TorsorIsoEquivFinalProbeAdapted
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

abbrev S3076B : Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  S3073PullbackTotal g (S3073PullbackFiber f P)

noncomputable abbrev S3076ToB' : S3076ToCActionProbe.S3076A f g P ⟶ S3076B f g P :=
  pullback.lift
    (S3076ToCActionProbe.S3076ToC' f g P)
    (pullback.snd (f := S3076CompE P)
      (g := (S3076CompG g) ≫ (S3076CompF f)))
    (by
      show S3076ToCActionProbe.S3076ToC' f g P ≫
          pullback.snd (f := S3076CompE P) (g := S3076CompF f) =
        pullback.snd (f := S3076CompE P)
          (g := (S3076CompG g) ≫ (S3076CompF f)) ≫ S3076CompG g
      rw [S3076ToCActionProbe.S3076ToC', pullback.lift_snd])


@[simp] lemma S3076ToB'_eq :
    S3076ToB' f g P =
      pullback.lift
        (S3076ToCActionProbe.S3076ToC' f g P)
        (pullback.snd (f := S3076CompE P)
          (g := (S3076CompG g) ≫ (S3076CompF f)))
        (by
          show S3076ToCActionProbe.S3076ToC' f g P ≫
              pullback.snd (f := S3076CompE P) (g := S3076CompF f) =
            pullback.snd (f := S3076CompE P)
              (g := (S3076CompG g) ≫ (S3076CompF f)) ≫ S3076CompG g
          rw [S3076ToCActionProbe.S3076ToC', pullback.lift_snd]) := rfl

theorem S3076Equiv (h : SignGroup) :
    S3076ToB' f g P ≫
      S3073PullbackAction g (S3073PullbackFiber f P) h =
    S3073PullbackAction (f ≫ g) P h ≫ S3076ToB' f g P := by
  apply pullback.hom_ext
    (f := S3073PullbackProjection f P) (g := S3076CompG g)
  · rw [Category.assoc]
    rw [S3076ToCActionProbe.S3076Action_fst
      (F' := g) (Q := S3073PullbackFiber f P) (h := h)]
    rw [← Category.assoc]
    rw [S3076ToB'_eq, pullback.lift_fst]
    rw [S3076ToCActionProbe.S3076ToC_action]
    rw [Category.assoc]
    rw [pullback.lift_fst]
  · rw [Category.assoc]
    rw [S3076ToCActionProbe.S3076Action_snd
      (F' := g) (Q := S3073PullbackFiber f P) (h := h)]
    rw [S3076ToB'_eq, pullback.lift_snd]
    rw [Category.assoc]
    rw [pullback.lift_snd]
    rw [pullback.lift_snd]
    rw [← S3076ToCActionProbe.S3076Action_snd (F' := f ≫ g) (Q := P) (h := h)]

#check S3076ToB'
#check S3076Equiv
end LeanFormal.IUT.XiFPaper.S3076TorsorIsoEquivFinalProbeAdapted
end

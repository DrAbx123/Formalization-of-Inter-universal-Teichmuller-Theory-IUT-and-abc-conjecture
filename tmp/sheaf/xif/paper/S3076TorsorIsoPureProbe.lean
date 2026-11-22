import tmp.sheaf.xif.paper.S3076ToCActionProbe
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
namespace LeanFormal.IUT.XiFPaper.S3076TorsorIsoPureProbe

abbrev Cbase : Type 1 := Iut.SchemeOverField S2994A6Stackification.S2994A6K
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

abbrev A {U V W : LocallyDiscrete Cbaseᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) :
    Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  pullback P.projection (g.as.unop ≫ f.as.unop)

abbrev C {U V : LocallyDiscrete Cbaseᵒᵖ} (f : U ⟶ V)
    (P : S3048SignTorsorFiber U) :
    Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  pullback P.projection f.as.unop

abbrev B {U V W : LocallyDiscrete Cbaseᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) :
    Iut.SchemeOverField S2994A6Stackification.S2994A6K :=
  pullback (pullback.snd P.projection f.as.unop) g.as.unop

abbrev toC' {U V W : LocallyDiscrete Cbaseᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) : A f g P ⟶ C f P :=
  pullback.lift
    (pullback.fst (f := P.projection) (g := g.as.unop ≫ f.as.unop))
    (pullback.snd (f := P.projection) (g := g.as.unop ≫ f.as.unop) ≫ g.as.unop)
    (by
      rw [Category.assoc]
      exact pullback.condition)

abbrev toB' {U V W : LocallyDiscrete Cbaseᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) : A f g P ⟶ B f g P :=
  pullback.lift
    (toC' f g P)
    (pullback.snd (f := P.projection) (g := g.as.unop ≫ f.as.unop))
    (by
      show toC' f g P ≫ pullback.snd (f := P.projection) (g := f.as.unop) =
        pullback.snd (f := P.projection) (g := g.as.unop ≫ f.as.unop) ≫ g.as.unop
      rw [toC', pullback.lift_snd])

theorem toC'_action {U V W : LocallyDiscrete Cbaseᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) (h : SignGroup) :
    toC' f g P ≫ S3073PullbackAction f P h =
      S3073PullbackAction (f ≫ g) P h ≫ toC' f g P := by
  apply pullback.hom_ext (f := P.projection) (g := f.as.unop)
  · calc
      (toC' f g P ≫ S3073PullbackAction f P h) ≫ pullback.fst (f := P.projection) (g := f.as.unop)
          = toC' f g P ≫ (S3073PullbackAction f P h ≫
              pullback.fst (f := P.projection) (g := f.as.unop)) := by rw [Category.assoc]
      _ = toC' f g P ≫ (pullback.fst (f := P.projection) (g := f.as.unop) ≫ P.action h) := by
            rw [S3076ToCActionProbe.S3076Action_fst]
      _ = (toC' f g P ≫ pullback.fst (f := P.projection) (g := f.as.unop)) ≫ P.action h := by
            rw [Category.assoc]
      _ = pullback.fst (f := P.projection) (g := g.as.unop ≫ f.as.unop) ≫ P.action h := by
            rw [toC', pullback.lift_fst]
      _ = S3073PullbackAction (f ≫ g) P h ≫
            pullback.fst (f := P.projection) (g := g.as.unop ≫ f.as.unop) := by
            rw [← S3076ToCActionProbe.S3076Action_fst]
      _ = S3073PullbackAction (f ≫ g) P h ≫
            (toC' f g P ≫ pullback.fst (f := P.projection) (g := f.as.unop)) := by
            rw [toC', pullback.lift_fst]
      _ = (S3073PullbackAction (f ≫ g) P h ≫ toC' f g P) ≫
            pullback.fst (f := P.projection) (g := f.as.unop) := by rw [Category.assoc]
  · calc
      (toC' f g P ≫ S3073PullbackAction f P h) ≫ pullback.snd (f := P.projection) (g := f.as.unop)
          = toC' f g P ≫ (S3073PullbackAction f P h ≫
              pullback.snd (f := P.projection) (g := f.as.unop)) := by rw [Category.assoc]
      _ = toC' f g P ≫ pullback.snd (f := P.projection) (g := f.as.unop) := by
            rw [S3076ToCActionProbe.S3076Action_snd]
      _ = pullback.snd (f := P.projection) (g := g.as.unop ≫ f.as.unop) ≫ g.as.unop := by
            rw [toC', pullback.lift_snd]
      _ = S3073PullbackAction (f ≫ g) P h ≫
            (pullback.snd (f := P.projection) (g := g.as.unop ≫ f.as.unop) ≫ g.as.unop) := by
            rw [← Category.assoc, S3076ToCActionProbe.S3076Action_snd]
      _ = S3073PullbackAction (f ≫ g) P h ≫
            (toC' f g P ≫ pullback.snd (f := P.projection) (g := f.as.unop)) := by
            rw [toC', pullback.lift_snd]
      _ = (S3073PullbackAction (f ≫ g) P h ≫ toC' f g P) ≫
            pullback.snd (f := P.projection) (g := f.as.unop) := by rw [Category.assoc]

theorem hEqv {U V W : LocallyDiscrete Cbaseᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) (h : SignGroup) :
    toB' f g P ≫ S3073PullbackAction g (S3073PullbackFiber f P) h =
      S3073PullbackAction (f ≫ g) P h ≫ toB' f g P := by
  apply pullback.hom_ext
    (f := pullback.snd (f := P.projection) (g := f.as.unop)) (g := g.as.unop)
  · rw [Category.assoc]
    rw [S3076ToCActionProbe.S3076Action_fst (F' := g) (Q := S3073PullbackFiber f P) (h := h)]
    rw [← Category.assoc]
    rw [toB', pullback.lift_fst]
    rw [toC'_action]
    rw [Category.assoc]
    rw [toB', pullback.lift_fst]
  · rw [Category.assoc]
    rw [S3076ToCActionProbe.S3076Action_snd (F' := g) (Q := S3073PullbackFiber f P) (h := h)]
    rw [toB', pullback.lift_snd]
    rw [← S3076ToCActionProbe.S3076Action_snd (F' := f ≫ g) (Q := P) (h := h)]

#check toC'_action
#check hEqv
end LeanFormal.IUT.XiFPaper.S3076TorsorIsoPureProbe
end

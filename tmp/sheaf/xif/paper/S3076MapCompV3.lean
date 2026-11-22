import tmp.sheaf.xif.paper.S3073TorsorPullbackActual
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
namespace LeanFormal.IUT.XiFPaper.S3076MapCompV3
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K
variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

abbrev A : Iut.SchemeOverField S2994A6K :=
  (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P).total
abbrev Cc : Iut.SchemeOverField S2994A6K :=
  (S3073PullbackFiber (U := U) (V := V) (f := f) P).total
abbrev B : Iut.SchemeOverField S2994A6K :=
  (S3073PullbackFiber (U := V) (V := W) (f := g)
    (S3073PullbackFiber (U := U) (V := V) (f := f) P)).total

noncomputable def toC' : A f g P ⟶ Cc f P :=
  pullback.lift
    (pullback.fst (f := P.projection) (g := (f ≫ g).as.unop))
    (pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫ g.as.unop)
    (by
      calc
        pullback.fst (f := P.projection) (g := (f ≫ g).as.unop) ≫ P.projection
            = pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫
                (f ≫ g).as.unop := pullback.condition
        _ = (pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫
                g.as.unop) ≫ f.as.unop := by
              rw [show (f ≫ g).as.unop = g.as.unop ≫ f.as.unop from rfl,
                Category.assoc])

noncomputable def toB' : A f g P ⟶ B f g P :=
  pullback.lift
    (toC' f g P)
    (pullback.snd (f := P.projection) (g := (f ≫ g).as.unop))
    (by
      show toC' f g P ≫
          S3073PullbackProjection f P =
        pullback.snd (f := P.projection) (g := (f ≫ g).as.unop) ≫ g.as.unop
      unfold toC'
      rw [pullback.lift_snd])

#check A
#check B
#check Cc
#check toC'
#check toB'


theorem toC'_action (γ : Iut.SignGroup) :
    toC' f g P ≫ S3073PullbackAction f P γ =
      S3073PullbackAction (f ≫ g) P γ ≫ toC' f g P := by
  apply pullback.hom_ext (f := P.projection) (g := f.as.unop)
  · rw [Category.assoc]
    unfold S3073PullbackAction
    rw [pullback.lift_fst]
    conv_lhs => rw [← Category.assoc]
    unfold toC'
    rw [pullback.lift_fst]
    rw [Category.assoc]
    rw [pullback.lift_fst]
    rw [pullback.lift_fst]
  · rw [Category.assoc]
    unfold S3073PullbackAction
    rw [pullback.lift_snd]
    unfold toC'
    rw [pullback.lift_snd]
    rw [Category.assoc]
    rw [pullback.lift_snd]
    rw [← Category.assoc]
    rw [pullback.lift_snd]

#check toC'_action


theorem S3076Equiv (h : Iut.SignGroup) :
    toB' f g P ≫ S3073PullbackAction g (S3073PullbackFiber f P) h =
      S3073PullbackAction (f ≫ g) P h ≫ toB' f g P := by
  apply pullback.hom_ext
    (f := S3073PullbackProjection f P) (g := g.as.unop)
  · rw [Category.assoc]
    unfold S3073PullbackAction
    rw [pullback.lift_fst]
    conv_lhs => rw [← Category.assoc]
    unfold toB'
    rw [pullback.lift_fst]
    rw [Category.assoc]
    rw [pullback.lift_fst]
    change toC' f g P ≫ S3073PullbackAction f P h =
      S3073PullbackAction (f ≫ g) P h ≫ toC' f g P
    exact toC'_action f g P h
  · rw [Category.assoc]
    unfold S3073PullbackAction
    rw [pullback.lift_snd]
    unfold toB'
    rw [Category.assoc]
    rw [pullback.lift_snd]
    rw [pullback.lift_snd]

#check S3076Equiv
#print axioms S3076Equiv


noncomputable def S3076CompTorsorIsoV3
    (hIso : IsIso (toB' f g P)) :
    S3049TorsorIso W
      (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P)
      (S3073PullbackFiber (U := V) (V := W) (f := g)
        (S3073PullbackFiber (U := U) (V := V) (f := f) P)) where
  hom := toB' f g P
  comm := by
    unfold toB'
    rw [pullback.lift_snd]
  equivariant := S3076Equiv f g P
  isIso := hIso

#check S3076CompTorsorIsoV3
#print axioms S3076Equiv

end LeanFormal.IUT.XiFPaper.S3076MapCompV3
import tmp.sheaf.xif.paper.S3072QPrimePseudofunctor

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3071TorsorGroupoid
open LeanFormal.IUT.XiFPaper.S3072QPrimePseudofunctor
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual

noncomputable abbrev S3073PullbackTotal
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) (P : S3048SignTorsorFiber U) :
    Iut.SchemeOverField S2994A6K :=
  pullback P.projection f.as.unop

noncomputable abbrev S3073PullbackProjection
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) (P : S3048SignTorsorFiber U) :
    S3073PullbackTotal f P ⟶ Opposite.unop V.as :=
  pullback.snd (f := P.projection) (g := f.as.unop)


noncomputable abbrev S3073PullbackAction
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) (P : S3048SignTorsorFiber U) (g : SignGroup) :
    S3073PullbackTotal f P ⟶ S3073PullbackTotal f P :=
  pullback.lift (pullback.fst (f := P.projection) (g := f.as.unop) ≫ P.action g)
    (pullback.snd (f := P.projection) (g := f.as.unop)) (by
    calc
      (pullback.fst (f := P.projection) (g := f.as.unop) ≫ P.action g) ≫ P.projection
          = pullback.fst (f := P.projection) (g := f.as.unop) ≫ (P.action g ≫ P.projection) := by
              rw [Category.assoc]
      _ = pullback.fst (f := P.projection) (g := f.as.unop) ≫ P.projection := by rw [P.action_projection g]
      _ = pullback.snd (f := P.projection) (g := f.as.unop) ≫ f.as.unop := pullback.condition)

noncomputable abbrev S3073PullbackFiber
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) (P : S3048SignTorsorFiber U) :
    S3048SignTorsorFiber V where
  total := S3073PullbackTotal f P
  projection := S3073PullbackProjection f P
  action := S3073PullbackAction f P
  action_one := by
    apply pullback.hom_ext
    · simp only [S3073PullbackAction]
      rw [pullback.lift_fst, P.action_one]
      simp
    · simp only [S3073PullbackAction]
      rw [pullback.lift_snd]
      simp
  action_mul := by
    intro g h
    apply pullback.hom_ext
    · simp only [S3073PullbackAction]
      rw [pullback.lift_fst, P.action_mul]
      conv_rhs => rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        pullback.lift_fst]
      rw [Category.assoc]
    · simp only [S3073PullbackAction]
      rw [pullback.lift_snd]
      simp only [Category.assoc, pullback.lift_snd]
  action_projection := by
    intro g
    rw [S3073PullbackAction, pullback.lift_snd]
  simplyTransitive := P.simplyTransitive
  equivariantMap := pullback.fst (f := P.projection) (g := f.as.unop) ≫ P.equivariantMap
  equivariance := P.equivariance

#check S3073PullbackAction
#check S3073PullbackFiber

#check S3073PullbackTotal
#check S3073PullbackProjection

end LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
end

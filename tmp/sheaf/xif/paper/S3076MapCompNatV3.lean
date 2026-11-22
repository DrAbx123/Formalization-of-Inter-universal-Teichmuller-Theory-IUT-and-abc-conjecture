import tmp.sheaf.xif.paper.S3076MapCompV3
import tmp.sheaf.xif.paper.S3074PullbackFunctor
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3074PullbackFunctor
open LeanFormal.IUT.XiFPaper.S3076MapCompV3
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
namespace LeanFormal.IUT.XiFPaper.S3076MapCompNatV3
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable {P Q : S3048SignTorsorFiber U}

theorem S3076MapCompNatV3
    (I : ∀ (P : S3048SignTorsorFiber U),
      LeanFormal.IUT.XiFPaper.S3076MapCompV3.A f g P ≅
        LeanFormal.IUT.XiFPaper.S3076MapCompV3.B f g P)
    (hI : ∀ (P : S3048SignTorsorFiber U),
      (I P).hom = LeanFormal.IUT.XiFPaper.S3076MapCompV3.toB' f g P)
    (h : S3049TorsorIso U P Q) :
    (S3074MapIso (f ≫ g) h).hom ≫ (I Q).hom =
      (I P).hom ≫ (S3074MapIso g (S3074MapIso f h)).hom := by
  rw [hI P, hI Q]
  apply pullback.hom_ext
    (f := S3073PullbackProjection f Q) (g := g.as.unop)
  · apply pullback.hom_ext (f := Q.projection) (g := f.as.unop)
    · rw [Category.assoc]
      simp [LeanFormal.IUT.XiFPaper.S3076MapCompV3.toB',
        LeanFormal.IUT.XiFPaper.S3076MapCompV3.toC',
        S3074MapIso, S3074Map, S3073PullbackAction,
        pullback.lift_fst, pullback.lift_snd, Category.assoc, h.comm]
    · rw [Category.assoc]
      simp [LeanFormal.IUT.XiFPaper.S3076MapCompV3.toB',
        LeanFormal.IUT.XiFPaper.S3076MapCompV3.toC',
        S3074MapIso, S3074Map, S3073PullbackAction,
        pullback.lift_fst, pullback.lift_snd, Category.assoc, h.comm]
  · rw [Category.assoc]
    simp [LeanFormal.IUT.XiFPaper.S3076MapCompV3.toB',
      LeanFormal.IUT.XiFPaper.S3076MapCompV3.toC',
      S3074MapIso, S3074Map, S3073PullbackAction,
      pullback.lift_fst, pullback.lift_snd, Category.assoc, h.comm]

#check S3076MapCompNatV3
end LeanFormal.IUT.XiFPaper.S3076MapCompNatV3
end

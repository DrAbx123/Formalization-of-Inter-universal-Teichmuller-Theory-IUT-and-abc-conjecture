import tmp.sheaf.xif.paper.S3076QPrimeMapCompActual
import tmp.sheaf.xif.paper.S3074PullbackFunctor
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3074PullbackFunctor
namespace LeanFormal.IUT.XiFPaper.S3076MapCompNatProbe2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable {P Q : S3048SignTorsorFiber U}

theorem S3076MapCompNat
    (h : S3049TorsorIso U P Q) :
    (S3074MapIso (f ≫ g) h).hom ≫
        (S3076CompTotalIso f g Q).hom =
      (S3076CompTotalIso f g P).hom ≫
        (S3074MapIso g (S3074MapIso f h)).hom := by
  apply pullback.hom_ext
    (f := pullback.snd (f := S3076CompE Q) (g := S3076CompF f))
    (g := S3076CompG g)
  · apply pullback.hom_ext (f := Q.projection) (g := f.as.unop)
    · rw [Category.assoc]
      simp [S3074MapIso, S3074Map, S3076CompTotalIso, S3076CompToA,
        S3076CompToB, pullback.lift_fst, pullback.lift_snd,
        Category.assoc, h.comm]
    · rw [Category.assoc]
      simp [S3074MapIso, S3074Map, S3076CompTotalIso, S3076CompToA,
        S3076CompToB, pullback.lift_fst, pullback.lift_snd,
        Category.assoc, h.comm]
  · simp [S3074MapIso, S3074Map, S3076CompTotalIso, S3076CompToA,
      S3076CompToB, pullback.lift_fst, pullback.lift_snd, Category.assoc, h.comm]

#check S3076CompTotalIso
#check S3076MapCompNat
end LeanFormal.IUT.XiFPaper.S3076MapCompNatProbe2
end

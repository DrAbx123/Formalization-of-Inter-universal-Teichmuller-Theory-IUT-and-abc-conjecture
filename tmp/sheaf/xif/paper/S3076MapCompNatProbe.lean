import tmp.sheaf.xif.paper.S3076ToCActionProbe
import tmp.sheaf.xif.paper.S3076CompUnitProbe
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
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
namespace LeanFormal.IUT.XiFPaper.S3076MapCompNatProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable {P Q : S3048SignTorsorFiber U}

theorem S3076MapCompNat
    (_hEqv : ∀ (P : S3048SignTorsorFiber U) (h : SignGroup),
      S3076CompUnitProbe.S3076CompToB f g P ≫
        S3073PullbackAction g (S3073PullbackFiber f P) h =
      S3073PullbackAction (f ≫ g) P h ≫
        S3076CompUnitProbe.S3076CompToB f g P)
    (h : S3049TorsorIso U P Q) :
    (S3074MapIso (f ≫ g) h).hom ≫
        (S3076CompUnitProbe.S3076CompIsoObj f g Q).hom =
      (S3076CompUnitProbe.S3076CompIsoObj f g P).hom ≫
        (S3074MapIso g (S3074MapIso f h)).hom := by
  apply pullback.hom_ext
    (f := pullback.snd (f := S3076CompE Q) (g := S3076CompF f))
    (g := S3076CompG g)
  · simp [S3074MapIso, S3074Map, S3076CompUnitProbe.S3076CompIsoObj,
      S3076CompUnitProbe.S3076CompToA, S3076CompUnitProbe.S3076CompToB,
      pullback.lift_fst, pullback.lift_snd, Category.assoc, h.comm]
  · simp [S3074MapIso, S3074Map, S3076CompUnitProbe.S3076CompIsoObj,
      S3076CompUnitProbe.S3076CompToA, S3076CompUnitProbe.S3076CompToB,
      pullback.lift_fst, pullback.lift_snd, Category.assoc, h.comm]

#check S3076MapCompNat
end LeanFormal.IUT.XiFPaper.S3076MapCompNatProbe
end

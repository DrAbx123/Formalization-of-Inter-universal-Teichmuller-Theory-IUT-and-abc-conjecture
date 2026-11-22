import tmp.sheaf.xif.paper.S3076CompTorsorIsoActual
import tmp.sheaf.xif.paper.S3076ToCActionProbe2
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
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
open LeanFormal.IUT.XiFPaper.S3076TorsorIsoCommProbe
open LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoActual
open LeanFormal.IUT.XiFPaper.S3076ToCActionProbe2
namespace LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoEqvProbeAdapted
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K
variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U) (γ : Iut.SignGroup)

theorem S3076CompEquiv :
    S3076CompToB f g P ≫
      (S3073PullbackFiber (U := V) (V := W) (f := g)
        (S3073PullbackFiber (U := U) (V := V) (f := f) P)).action γ =
    (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P).action γ ≫
      S3076CompToB f g P := by
  apply pullback.hom_ext
    (f := pullback.snd (S3076CompE P) (S3076CompF f))
    (g := S3076CompG g)
  · rw [Category.assoc]
    simp only [S3073PullbackAction, pullback.lift_fst]
    rw [Category.assoc]
    rw [S3076CompToB, pullback.lift_fst]
    rw [Category.assoc]
    rw [S3076CompToB, pullback.lift_fst]
    change toC f g P ≫ actionC f P γ = actionA f g P γ ≫ toC f g P
    exact toC_action f g P γ
  · rw [Category.assoc]
    simp only [S3073PullbackAction, pullback.lift_snd]
    rw [S3076CompToB, pullback.lift_snd]
    rw [Category.assoc]
    rw [S3073PullbackAction, pullback.lift_snd]

#check S3076CompEquiv

noncomputable def S3076CompTorsorIsoUnconditional :
    S3049TorsorIso W
      (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P)
      (S3073PullbackFiber (U := V) (V := W) (f := g)
        (S3073PullbackFiber (U := U) (V := V) (f := f) P)) :=
  S3076CompTorsorIso f g P (S3076CompEquiv f g P)

#check S3076CompTorsorIsoUnconditional

end LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoEqvProbeAdapted
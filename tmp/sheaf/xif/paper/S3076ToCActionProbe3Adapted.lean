import tmp.sheaf.xif.paper.S3076QPrimeMapCompActual
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
namespace LeanFormal.IUT.XiFPaper.S3076ToCActionProbe3Adapted
set_option maxHeartbeats 4000000
abbrev C : Type 1 := Iut.SchemeOverField S2994A6K

abbrev A {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) : Iut.SchemeOverField S2994A6K :=
  (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P).total
abbrev Cc {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (P : S3048SignTorsorFiber U) : Iut.SchemeOverField S2994A6K :=
  (S3073PullbackFiber (U := U) (V := V) (f := f) P).total

noncomputable def toC {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) : A f g P ⟶ Cc f P :=
  S3076CompToC f g P

theorem toC_action {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (P : S3048SignTorsorFiber U) (γ : Iut.SignGroup) :
    toC f g P ≫ (S3073PullbackFiber (U := U) (V := V) (f := f) P).action γ =
      (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P).action γ ≫ toC f g P := by
  apply pullback.hom_ext
    (f := P.projection) (g := f.as.unop)
  · simp only [toC, S3076CompToC, S3073PullbackAction, Category.assoc]
    rw [Category.assoc, pullback.lift_fst]
    rw [Category.assoc, pullback.lift_fst]
    rw [pullback.lift_fst]
  · simp only [toC, S3076CompToC, S3073PullbackAction, Category.assoc]
    rw [Category.assoc, pullback.lift_snd]
    rw [pullback.lift_snd]
    rw [Category.assoc, pullback.lift_snd]
    rw [Category.assoc]

#check toC_action

end LeanFormal.IUT.XiFPaper.S3076ToCActionProbe3Adapted
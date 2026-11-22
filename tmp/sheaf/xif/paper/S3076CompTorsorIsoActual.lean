import tmp.sheaf.xif.paper.S3076TorsorIsoCommProbe
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
namespace LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoActual
set_option maxHeartbeats 4000000

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K
variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

noncomputable def S3076CompTorsorIso
    (hEqv : ∀ γ : Iut.SignGroup,
      S3076CompToB f g P ≫
        (S3073PullbackFiber (U := V) (V := W) (f := g)
          (S3073PullbackFiber (U := U) (V := V) (f := f) P)).action γ =
      (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P).action γ ≫
        S3076CompToB f g P) :
    S3049TorsorIso W
      (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P)
      (S3073PullbackFiber (U := V) (V := W) (f := g)
        (S3073PullbackFiber (U := U) (V := V) (f := f) P)) where
  hom := S3076CompToB f g P
  comm := S3076CompComm f g P
  equivariant := hEqv
  isIso := (S3076CompTotalIso f g P).isIso_hom

#check S3076CompTorsorIso
#check @S3076CompTorsorIso

end LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoActual
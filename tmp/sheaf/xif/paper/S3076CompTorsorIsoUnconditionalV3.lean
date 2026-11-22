import tmp.sheaf.xif.paper.S3076MapCompV3
import tmp.sheaf.xif.paper.S3076QPrimeMapCompActual
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
open LeanFormal.IUT.XiFPaper.S3076MapCompV3
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
namespace LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoUnconditionalV3
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
abbrev C : Type 1 := Iut.SchemeOverField S2994A6K
variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

noncomputable def S3076CompTorsorIsoUnconditionalV3 :
    S3049TorsorIso W
      (S3073PullbackFiber (U := U) (V := W) (f := f ≫ g) P)
      (S3073PullbackFiber (U := V) (V := W) (f := g)
        (S3073PullbackFiber (U := U) (V := V) (f := f) P)) :=
  S3076CompTorsorIsoV3 f g P (by
    change IsIso (S3076CompToB f g P)
    exact (S3076CompTotalIso f g P).isIso_hom)

#check S3076CompTorsorIsoUnconditionalV3
#print axioms S3076CompTorsorIsoUnconditionalV3

end LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoUnconditionalV3
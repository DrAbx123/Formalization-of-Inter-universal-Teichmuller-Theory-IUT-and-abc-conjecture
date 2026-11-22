import tmp.sheaf.xif.paper.S3076MapCompNatV3
import tmp.sheaf.xif.paper.S3076CompTorsorIsoUnconditionalV3
import tmp.sheaf.xif.paper.S3076MapCompV3IsoProbe
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3074PullbackFunctor
open LeanFormal.IUT.XiFPaper.S3076MapCompV3
open LeanFormal.IUT.XiFPaper.S3076MapCompNatV3
namespace LeanFormal.IUT.XiFPaper.S3076MapCompNatUnconditionalV3
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable {P Q : S3048SignTorsorFiber U}

theorem S3076MapCompNatUnconditionalV3
    (h : S3049TorsorIso U P Q) :
    (S3074MapIso (f ≫ g) h).hom ≫
        (LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g Q).hom =
      (LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g P).hom ≫
        (S3074MapIso g (S3074MapIso f h)).hom :=
  S3076MapCompNatV3 f g
    (fun (P : S3048SignTorsorFiber U) =>
      Iso.mk
        (LeanFormal.IUT.XiFPaper.S3076MapCompV3.toB' f g P)
        (LeanFormal.IUT.XiFPaper.S3076MapCompV3IsoProbe.toA' f g P)
        (LeanFormal.IUT.XiFPaper.S3076MapCompV3IsoProbe.toB'_toA' f g P)
        (LeanFormal.IUT.XiFPaper.S3076MapCompV3IsoProbe.toA'_toB' f g P))
    (fun (P : S3048SignTorsorFiber U) => rfl)
    h

#check S3076MapCompNatUnconditionalV3
end LeanFormal.IUT.XiFPaper.S3076MapCompNatUnconditionalV3
end

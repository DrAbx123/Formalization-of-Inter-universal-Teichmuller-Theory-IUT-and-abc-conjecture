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
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
namespace LeanFormal.IUT.XiFPaper.S3076MapCompV3IsoProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

variable {U V W : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

noncomputable abbrev toA' :
    LeanFormal.IUT.XiFPaper.S3076MapCompV3.B f g P ⟶
      LeanFormal.IUT.XiFPaper.S3076MapCompV3.A f g P :=
  S3076CompToA f g P

theorem toB'_toA' :
    LeanFormal.IUT.XiFPaper.S3076MapCompV3.toB' f g P ≫ toA' f g P =
      𝟙 (LeanFormal.IUT.XiFPaper.S3076MapCompV3.A f g P) :=
  S3076CompToB_toA f g P

theorem toA'_toB' :
    toA' f g P ≫ LeanFormal.IUT.XiFPaper.S3076MapCompV3.toB' f g P =
      𝟙 (LeanFormal.IUT.XiFPaper.S3076MapCompV3.B f g P) :=
  S3076CompToA_toB f g P

noncomputable def toB'_isIso :
    IsIso (LeanFormal.IUT.XiFPaper.S3076MapCompV3.toB' f g P) :=
  ⟨toA' f g P, toB'_toA' f g P, toA'_toB' f g P⟩

#check toA'
#check toB'_toA'
#check toA'_toB'
#check toB'_isIso
end LeanFormal.IUT.XiFPaper.S3076MapCompV3IsoProbe
end

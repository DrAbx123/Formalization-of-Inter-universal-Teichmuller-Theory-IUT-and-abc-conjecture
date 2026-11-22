import tmp.sheaf.xif.paper.S3076CompTorsorIsoUnconditionalV3
import tmp.sheaf.xif.paper.S3076MapCompNatUnconditionalV3
import tmp.sheaf.xif.paper.S3076MapCompV3IsoProbe
import tmp.sheaf.xif.paper.S3071TorsorGroupoid
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3071TorsorGroupoid
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
namespace LeanFormal.IUT.XiFPaper.S3078MapCompNatIsoActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

abbrev C : Type 1 := Iut.SchemeOverField S2994A6Stackification.S2994A6K
variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)

noncomputable def S3078MapCompNatIso :
    S3075PullbackFunctor (f ≫ g) ≅
      (S3075PullbackFunctor f ⋙ S3075PullbackFunctor g) :=
  NatIso.ofComponents
    (fun P =>
      Iso.mk
        (LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g P)
        (S3071IsoInv W
          (LeanFormal.IUT.XiFPaper.S3076CompTorsorIsoUnconditionalV3.S3076CompTorsorIsoUnconditionalV3 f g P))
        (by
          apply S3049TorsorIso.ext
          simp [S3071IsoInv])
        (by
          apply S3049TorsorIso.ext
          simp [S3071IsoInv]))
    (by
      intro P Q h
      apply S3049TorsorIso.ext
      simpa [S3075PullbackFunctor]
        using LeanFormal.IUT.XiFPaper.S3076MapCompNatUnconditionalV3.S3076MapCompNatUnconditionalV3 f g h)

#check S3078MapCompNatIso
#print axioms S3078MapCompNatIso
end LeanFormal.IUT.XiFPaper.S3078MapCompNatIsoActual
end

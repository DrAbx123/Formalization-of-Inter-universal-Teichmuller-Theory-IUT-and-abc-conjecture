import tmp.sheaf.xif.paper.S3075QPrimeAssembly
import tmp.sheaf.xif.paper.S3073TorsorPullbackActual
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
namespace LeanFormal.IUT.XiFPaper.S3073PullbackTotalBridge
set_option backward.isDefEq.respectTransparency false

variable {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ}
variable (f : U ⟶ V)
variable (P : S3048SignTorsorFiber U)

@[simp] lemma S3073PullbackTotal_eq_obj_total :
    S3073PullbackTotal f P =
      ((S3075PullbackFunctor f).obj P).total := rfl

@[simp] lemma obj_total_eq_S3073PullbackTotal :
    ((S3075PullbackFunctor f).obj P).total =
      S3073PullbackTotal f P := rfl

#check S3073PullbackTotal_eq_obj_total
#check obj_total_eq_S3073PullbackTotal
end LeanFormal.IUT.XiFPaper.S3073PullbackTotalBridge
end

import tmp.sheaf.xif.paper.S3123StackScalarExtensionFiberActual
import tmp.sheaf.xif.paper.S3123FiberEquivalenceOfDataOldActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123InvAppActual
open LeanFormal.IUT.XiFPaper.S3123InvNatActual
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataOldActual
open LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionActual
open LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionFiberActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionProjectionActual

variable {l : PrimeGeFive}


@[simp] theorem S3123StackScalarExtension_result :
    (S3123StackScalarExtension (l := l)).result = S3123Result (l := l) := rfl

@[simp] theorem S3123StackScalarExtension_fiberEquivalence :
    (S3123StackScalarExtension (l := l)).fiberEquivalence =
      S3123FiberEquivalenceOfDataOld (l := l) := rfl

noncomputable def S3123KCoreEtaleStack : EtaleStackOverField (S1280Arithmetic l).K :=
  S3123Result (l := l)

noncomputable def S3123KCoreFiberEquivalence :
    Bicategory.Equivalence (S3123KCoreEtaleStack (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber) :=
  S3123StackScalarExtensionFiberEquivalence (l := l)

#check S3123StackScalarExtension_result
#check S3123KCoreFiberEquivalence

end LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionProjectionActual
end

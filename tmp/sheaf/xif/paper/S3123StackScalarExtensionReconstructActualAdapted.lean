import tmp.sheaf.xif.paper.S3123StackScalarExtensionProjectionActualAdapted
import tmp.sheaf.xif.paper.S3123StackScalarExtensionOfActual

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
open LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionProjectionActualAdapted
open LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionOfActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionReconstructActualAdapted

variable {l : PrimeGeFive}


theorem S3123StackScalarExtension_reconstruct :
    S3123StackScalarExtension (l := l) =
      SourceEtaleStackScalarExtensionOf (S3123Result (l := l))
        (S3123FiberEquivalenceOfDataOld (l := l)) := rfl

#check S3123StackScalarExtension_reconstruct

end LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionReconstructActualAdapted
end

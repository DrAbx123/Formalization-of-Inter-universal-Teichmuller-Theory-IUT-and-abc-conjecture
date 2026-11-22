import tmp.sheaf.xif.paper.S3123FiberEquivalenceOfDataOldActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

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

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionActual

variable {l : PrimeGeFive}


set_option maxHeartbeats 800000 in
noncomputable def S3123StackScalarExtension :
    SourceEtaleStackScalarExtension (S1280Arithmetic l).F (S1280Arithmetic l).K
      (S1536XF (l := l)).stack where
  result := S3123Result (l := l)
  fiberEquivalence := S3123FiberEquivalenceOfDataOld (l := l)

#check S3123StackScalarExtension

end LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionActual
end

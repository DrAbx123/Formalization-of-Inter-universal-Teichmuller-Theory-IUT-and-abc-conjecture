import tmp.sheaf.xif.paper.S3123StackScalarExtensionActual

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

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionFiberActual

variable {l : PrimeGeFive}


noncomputable def S3123StackScalarExtensionFiberEquivalence :
    Bicategory.Equivalence (S3123Result (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber) :=
  (S3123StackScalarExtension (l := l)).fiberEquivalence

theorem S3123StackScalarExtension_nonempty :
    Nonempty (SourceEtaleStackScalarExtension (S1280Arithmetic l).F
      (S1280Arithmetic l).K (S1536XF (l := l)).stack) :=
  ⟨S3123StackScalarExtension (l := l)⟩

#check S3123StackScalarExtensionFiberEquivalence
#check S3123StackScalarExtension_nonempty

end LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionFiberActual
end

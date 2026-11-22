import tmp.sheaf.xif.paper.S3123StackScalarExtensionProjectionActual

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
open LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionProjectionActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionExistsActual

variable {l : PrimeGeFive}


theorem S3123StackScalarExtension_exists :
    ∃ (E : EtaleStackOverField (S1280Arithmetic l).K),
      Nonempty (Bicategory.Equivalence E.fiber
        (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
          (S1280Arithmetic l).F (S1280Arithmetic l).K)
          (S1536XF (l := l)).stack.fiber)) :=
  ⟨S3123Result (l := l), ⟨S3123FiberEquivalenceOfDataOld (l := l)⟩⟩

theorem S3123StackScalarExtension_fiber_nonempty :
    Nonempty (Bicategory.Equivalence (S3123Result (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber)) :=
  ⟨S3123FiberEquivalenceOfDataOld (l := l)⟩

#check S3123StackScalarExtension_exists
#check S3123StackScalarExtension_fiber_nonempty

end LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionExistsActual
end

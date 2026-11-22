import tmp.sheaf.xif.paper.S3123SourceOrbicurveScalarExtensionOfStackNonemptyActual

universe u

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
open LeanFormal.IUT.XiFPaper.S3123UnitIsoOldActual
open LeanFormal.IUT.XiFPaper.S3123CounitIsoOldActual
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceFinalActual
open LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionActual
open LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessActual
open LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessOfStackActual
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfActual
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfStackActual
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfStackProjectionActual
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfStackReconstructActual
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfStackNonemptyActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfStackStackNonemptyActual

variable {l : PrimeGeFive}

theorem S3123SourceOrbicurveScalarExtensionOfStack_stack_nonempty
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    Nonempty (SourceEtaleStackScalarExtension (S1280Arithmetic l).F
      (S1280Arithmetic l).K (S1536XF (l := l)).stack) :=
  ⟨(S3123SourceOrbicurveScalarExtensionOfStack (l := l) R hR hgenus).stackExtension⟩

theorem S3123SourceOrbicurveScalarExtensionOfStack_fiber_nonempty
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    Nonempty (Bicategory.Equivalence (S3123Result (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber)) :=
  ⟨(S3123SourceOrbicurveScalarExtensionOfStack (l := l) R hR hgenus).stackExtension.fiberEquivalence⟩

#check S3123SourceOrbicurveScalarExtensionOfStack_stack_nonempty
#check S3123SourceOrbicurveScalarExtensionOfStack_fiber_nonempty

end LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfStackStackNonemptyActual
end

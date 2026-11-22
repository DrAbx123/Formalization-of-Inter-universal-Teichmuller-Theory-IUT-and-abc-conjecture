import tmp.sheaf.xif.paper.S3123SourceOrbicurveScalarExtensionOfStackActualAdapted

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
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfStackActualAdapted

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfStackProjectionActualAdapted

variable {l : PrimeGeFive}

@[simp] theorem S3123SourceOrbicurveScalarExtensionOfStack_stack_result
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    (S3123SourceOrbicurveScalarExtensionOfStack (l := l) R hR hgenus).stackExtension.result =
      S3123Result (l := l) := rfl

@[simp] theorem S3123SourceOrbicurveScalarExtensionOfStack_fiberEquivalence
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    (S3123SourceOrbicurveScalarExtensionOfStack (l := l) R hR hgenus).stackExtension.fiberEquivalence =
      S3123FiberEquivalenceFinal (l := l) := rfl

#check S3123SourceOrbicurveScalarExtensionOfStack_stack_result
#check S3123SourceOrbicurveScalarExtensionOfStack_fiberEquivalence

end LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfStackProjectionActualAdapted
end

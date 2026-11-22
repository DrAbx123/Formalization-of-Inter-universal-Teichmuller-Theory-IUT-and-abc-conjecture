import tmp.sheaf.xif.paper.S3123StackScalarExtensionActual
import tmp.sheaf.xif.paper.S3123OrbicurveScalarExtensionWitnessActual

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

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessOfStackActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123OrbicurveScalarExtensionWitness.ofStack
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    S3123OrbicurveScalarExtensionWitness (S1280Arithmetic l).F
      (S1280Arithmetic l).K := 
  { X := S1536XF (l := l)
    R := R
    stackExtension := S3123StackScalarExtension (l := l)
    target_stack := hR
    genus_preserved := hgenus }

#check S3123OrbicurveScalarExtensionWitness.ofStack

end LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessOfStackActual
end

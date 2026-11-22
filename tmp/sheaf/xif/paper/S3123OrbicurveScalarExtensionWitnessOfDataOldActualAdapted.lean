import tmp.sheaf.xif.paper.S3123SourceEtaleStackScalarExtensionOfDataOldActualAdapted
import tmp.sheaf.xif.paper.S3123OrbicurveScalarExtensionWitnessActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped Pseudofunctor.StrongTrans
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
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataOldActual
open LeanFormal.IUT.XiFPaper.S3123CounitIsoDataOldActual
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataActual
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataOldActual
open LeanFormal.IUT.XiFPaper.S3123SourceEtaleStackScalarExtensionOfDataOldActualAdapted
open LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessActual
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessOfDataOldActualAdapted

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123OrbicurveScalarExtensionWitness.ofDataOld
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    S3123OrbicurveScalarExtensionWitness (S1280Arithmetic l).F
      (S1280Arithmetic l).K :=
  { X := S1536XF (l := l)
    R := R
    stackExtension := S3123SourceEtaleStackScalarExtensionOfDataOld (l := l)
    target_stack := hR
    genus_preserved := hgenus }

#check S3123OrbicurveScalarExtensionWitness.ofDataOld

end LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessOfDataOldActualAdapted
end

import tmp.sheaf.xif.paper.S3123SourceOrbicurveScalarExtensionOfDataOldActualAdapted

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
open LeanFormal.IUT.XiFPaper.S3123SourceEtaleStackScalarExtensionOfDataOldActual
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfActual
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfDataOldActualAdapted

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfDataOldProjectionActualAdapted

variable {l : PrimeGeFive}

@[simp] theorem S3123SourceOrbicurveScalarExtensionOfDataOld_result
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    (S3123SourceOrbicurveScalarExtensionOfDataOld (l := l) R hR hgenus).result =
      R := rfl

@[simp] theorem S3123SourceOrbicurveScalarExtensionOfDataOld_stackExtension
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    (S3123SourceOrbicurveScalarExtensionOfDataOld (l := l) R hR hgenus).stackExtension =
      S3123SourceEtaleStackScalarExtensionOfDataOld (l := l) := rfl

theorem S3123SourceOrbicurveScalarExtensionOfDataOld_fiber_nonempty
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    Nonempty (Bicategory.Equivalence (S3123Result (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber)) :=
  ⟨S3123FiberEquivalenceOfDataOld (l := l)⟩

#check S3123SourceOrbicurveScalarExtensionOfDataOld_result
#check S3123SourceOrbicurveScalarExtensionOfDataOld_fiber_nonempty

end LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfDataOldProjectionActualAdapted
end

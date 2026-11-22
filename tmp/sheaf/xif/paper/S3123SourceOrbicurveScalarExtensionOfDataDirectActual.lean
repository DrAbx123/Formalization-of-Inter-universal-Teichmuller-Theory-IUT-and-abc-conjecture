import tmp.sheaf.xif.paper.S3123SourceEtaleStackScalarExtensionOfDataDirectActual
import tmp.sheaf.xif.paper.S3123SourceOrbicurveScalarExtensionOfActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped Pseudofunctor.StrongTrans
open CategoryTheory.Pseudofunctor.StrongTrans
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
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataActual
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataDirectActual
open LeanFormal.IUT.XiFPaper.S3123SourceEtaleStackScalarExtensionOfDataDirectActual
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfDataDirectActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123SourceOrbicurveScalarExtensionOfDataDirect
    (η : S3123UnitIsoData (l := l))
    (ε : S3123CounitIsoData (l := l))
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    SourceOrbicurveScalarExtension (S1280Arithmetic l).F (S1280Arithmetic l).K
      (S1536XF (l := l)) :=
  SourceOrbicurveScalarExtensionOf R
    (S3123SourceEtaleStackScalarExtensionOfDataDirect (l := l) η ε) hR hgenus

theorem S3123SourceOrbicurveScalarExtensionOfDataDirect_nonempty
    (η : S3123UnitIsoData (l := l))
    (ε : S3123CounitIsoData (l := l))
    (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus) :
    Nonempty (SourceOrbicurveScalarExtension (S1280Arithmetic l).F
      (S1280Arithmetic l).K (S1536XF (l := l))) :=
  ⟨S3123SourceOrbicurveScalarExtensionOfDataDirect (l := l) η ε R hR hgenus⟩

#check S3123SourceOrbicurveScalarExtensionOfDataDirect
#check S3123SourceOrbicurveScalarExtensionOfDataDirect_nonempty

end LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfDataDirectActual
end

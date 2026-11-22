import tmp.sheaf.xif.paper.S3123FiberEquivalenceOfDataDirectActual
import tmp.sheaf.xif.paper.S3123UnitIsoDataActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

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

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123SourceEtaleStackScalarExtensionOfDataDirectActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123SourceEtaleStackScalarExtensionOfDataDirect
    (η : S3123UnitIsoData (l := l))
    (ε : S3123CounitIsoData (l := l)) :
    SourceEtaleStackScalarExtension (S1280Arithmetic l).F (S1280Arithmetic l).K
      (S1536XF (l := l)).stack :=
  ⟨S3123Result (l := l), S3123FiberEquivalenceOfDataDirect (l := l) η ε⟩

theorem S3123SourceEtaleStackScalarExtensionOfDataDirect_nonempty
    (η : S3123UnitIsoData (l := l))
    (ε : S3123CounitIsoData (l := l)) :
    Nonempty (SourceEtaleStackScalarExtension (S1280Arithmetic l).F
      (S1280Arithmetic l).K (S1536XF (l := l)).stack) :=
  ⟨S3123SourceEtaleStackScalarExtensionOfDataDirect (l := l) η ε⟩

#check S3123SourceEtaleStackScalarExtensionOfDataDirect
#check S3123SourceEtaleStackScalarExtensionOfDataDirect_nonempty

end LeanFormal.IUT.XiFPaper.S3123SourceEtaleStackScalarExtensionOfDataDirectActual
end

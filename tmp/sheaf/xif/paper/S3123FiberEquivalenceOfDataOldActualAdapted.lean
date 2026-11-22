import tmp.sheaf.xif.paper.S3123UnitIsoDataOldActual
import tmp.sheaf.xif.paper.S3123CounitIsoDataOldActual
import tmp.sheaf.xif.paper.S3123FiberEquivalenceOfDataActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
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

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataOldActualAdapted

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123FiberEquivalenceOfDataOld :
    Bicategory.Equivalence (S3123Result (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber) :=
  S3123FiberEquivalenceOfData (l := l)
    (S3123UnitIsoDataOld (l := l))
    (S3123CounitIsoDataOld (l := l))

#check S3123FiberEquivalenceOfDataOld

end LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataOldActualAdapted
end

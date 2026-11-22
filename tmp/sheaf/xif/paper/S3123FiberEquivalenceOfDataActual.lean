import tmp.sheaf.xif.paper.S3123UnitIsoDataActual
import tmp.sheaf.xif.paper.S3123FiberEquivalenceBuilderActual

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
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceBuilderActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataActual

variable {l : PrimeGeFive}


set_option maxHeartbeats 800000 in
noncomputable def S3123FiberEquivalenceOfData
    (ηd : S3123UnitIsoData (l := l))
    (εd : S3123CounitIsoData (l := l)) :
    Bicategory.Equivalence (S3123Result (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber) :=
  S3123FiberEquivalenceOf (l := l) ηd.toIso εd.toIso

#check S3123FiberEquivalenceOfData

end LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataActual
end

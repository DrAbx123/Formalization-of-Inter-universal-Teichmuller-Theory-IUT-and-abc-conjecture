import tmp.sheaf.xif.paper.S3123FiberEquivalenceOfDataActual
import tmp.sheaf.xif.paper.S3123UnitIsoDataActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped Pseudofunctor.StrongTrans
open CategoryTheory.Pseudofunctor.StrongTrans
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
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataDirectActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123FiberEquivalenceOfDataDirect
    (η : S3123UnitIsoData (l := l))
    (ε : S3123CounitIsoData (l := l)) :
    Bicategory.Equivalence (S3123Result (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber) :=
  S3123FiberEquivalenceOfData (l := l) η ε

theorem S3123FiberEquivalenceOfDataDirect_nonempty
    (η : S3123UnitIsoData (l := l))
    (ε : S3123CounitIsoData (l := l)) :
    Nonempty (Bicategory.Equivalence (S3123Result (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber)) :=
  ⟨S3123FiberEquivalenceOfDataDirect (l := l) η ε⟩

#check S3123FiberEquivalenceOfDataDirect
#check S3123FiberEquivalenceOfDataDirect_nonempty

end LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceOfDataDirectActual
end

import tmp.sheaf.xif.paper.S3123StrongInvActual

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
open LeanFormal.IUT.XiFPaper.S3123ObjEqActual
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual

namespace LeanFormal.IUT.XiFPaper.S3123EquivActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123FiberEquivalence :
    Bicategory.Equivalence (S3123Result (l := l)).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
        (S1280Arithmetic l).F (S1280Arithmetic l).K)
        (S1536XF (l := l)).stack.fiber) := by
  refine Bicategory.Equivalence.mkOfAdjointifyCounit
    (f := S3123FiberStrongTrans (l := l))
    (g := S3123FiberStrongTransInv (l := l))
    (η := ?_) (ε := ?_)
  · exact eqToIso (by rfl)
  · exact eqToIso (by rfl)

#check S3123FiberEquivalence

end LeanFormal.IUT.XiFPaper.S3123EquivActual
end

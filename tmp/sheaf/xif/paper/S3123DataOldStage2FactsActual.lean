import tmp.sheaf.xif.paper.S3123DataOldExistenceActual
import tmp.sheaf.xif.paper.S3123SourceEtaleStackScalarExtensionOfDataOldProjectionActual

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
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfDataOldActual
open LeanFormal.IUT.XiFPaper.S3123DataOldExistenceActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123DataOldStage2FactsActual

variable {l : PrimeGeFive}

structure S3123DataOldStage2Facts where
  stack_nonempty : Nonempty (SourceEtaleStackScalarExtension (S1280Arithmetic l).F
    (S1280Arithmetic l).K (S1536XF (l := l)).stack)
  orbicurve_nonempty : ∀ (R : Iut.HyperbolicOrbicurve (S1280Arithmetic l).K)
    (hR : R.stack = S3123Result (l := l))
    (hgenus : R.signature.genus = (S1536XF (l := l)).signature.genus),
    Nonempty (SourceOrbicurveScalarExtension (S1280Arithmetic l).F
      (S1280Arithmetic l).K (S1536XF (l := l)))
  fiber_nonempty : Nonempty (Bicategory.Equivalence (S3123Result (l := l)).fiber
    (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
      (S1280Arithmetic l).F (S1280Arithmetic l).K)
      (S1536XF (l := l)).stack.fiber))

noncomputable def S3123DataOldStage2Facts.ofDataOld :
    S3123DataOldStage2Facts (l := l) :=
  { stack_nonempty := S3123SourceEtaleStackScalarExtensionOfDataOld_nonempty (l := l)
    orbicurve_nonempty := fun R hR hgenus =>
      S3123SourceOrbicurveScalarExtensionOfDataOld_nonempty (l := l) R hR hgenus
    fiber_nonempty := S3123SourceEtaleStackScalarExtensionOfDataOld_fiber_nonempty (l := l) }

#check S3123DataOldStage2Facts.ofDataOld

end LeanFormal.IUT.XiFPaper.S3123DataOldStage2FactsActual
end

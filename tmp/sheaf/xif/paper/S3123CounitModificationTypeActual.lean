import tmp.sheaf.xif.paper.S3123StrongInvActual
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

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

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123CounitModificationTypeActual

variable {l : PrimeGeFive}

abbrev S3123CounitModificationType : Type :=
  Pseudofunctor.StrongTrans.Modification
    (η := S3123FiberStrongTransInv (l := l) ≫ S3123FiberStrongTrans (l := l))
    (θ := 𝟙 (S3123Right (l := l)))

#check S3123CounitModificationType

end LeanFormal.IUT.XiFPaper.S3123CounitModificationTypeActual
end

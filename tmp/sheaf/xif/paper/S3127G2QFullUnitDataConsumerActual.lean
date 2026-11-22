import tmp.sheaf.xif.paper.S3127G2QFullUnitDataActual
import tmp.sheaf.xif.paper.S3127G2QFullUnitActionConsumerActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullUnitDataActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActionConsumerActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QFullUnitDataConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G]

structure S3127G2QFullUnitDataConsumer : Type 3 where
  data : S3127G2QFullUnitData A act
  actionData : S3127G2QFullUnitActionConsumer A act

noncomputable def S3127G2QFullUnitDataConsumer.of :
    S3127G2QFullUnitDataConsumer A act where
  data := S3127G2QFullUnitData.of A act
  actionData := S3127G2QFullUnitActionConsumer.of A act

#check S3127G2QFullUnitDataConsumer
#check S3127G2QFullUnitDataConsumer.of
end LeanFormal.IUT.XiFPaper.S3127G2QFullUnitDataConsumerActual
end

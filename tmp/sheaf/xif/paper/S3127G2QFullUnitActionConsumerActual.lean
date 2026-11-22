import tmp.sheaf.xif.paper.S3127G2QFullUnitActual
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActionConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G]

structure S3127G2QFullUnitActionConsumer  : Type 2 where
  cover : FiniteEtaleCover (S1419AffineScheme l)
  cover_eq : cover = S3127G2QFullUnit A act
  action_one : S3127G2Action A act 1 = 𝟙 A
  action_mul : ∀ g h : G,
    S3127G2Action A act (g * h) =
      S3127G2Action A act g ≫ S3127G2Action A act h

noncomputable def S3127G2QFullUnitActionConsumer.of :
    S3127G2QFullUnitActionConsumer A act where
  cover := S3127G2QFullUnit A act
  cover_eq := rfl
  action_one := S3127G2Action_one A act
  action_mul := S3127G2Action_mul A act

#check S3127G2QFullUnitActionConsumer
#check S3127G2QFullUnitActionConsumer.of
end LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActionConsumerActual
end

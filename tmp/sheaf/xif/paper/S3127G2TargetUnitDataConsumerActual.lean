import tmp.sheaf.xif.paper.S3127G2TargetUnitDataActual
import tmp.sheaf.xif.paper.S3127G2TargetUnitActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetUnitDataActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2TargetUnitDataConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

structure S3127G2TargetUnitDataConsumer : Type where
  targetData : S3127G2TargetUnitData A act hfree hInv
  target : S3127FreeQuotientTarget A G
  target_eq : target = targetData.target

noncomputable def S3127G2TargetUnitDataConsumer.of :
    S3127G2TargetUnitDataConsumer A act hfree hInv where
  targetData := S3127G2TargetUnitData.of A act hfree hInv
  target := S3127FreeQuotientTargetUnit A act hfree hInv
  target_eq := rfl

#check S3127G2TargetUnitDataConsumer
#check S3127G2TargetUnitDataConsumer.of
end LeanFormal.IUT.XiFPaper.S3127G2TargetUnitDataConsumerActual
end

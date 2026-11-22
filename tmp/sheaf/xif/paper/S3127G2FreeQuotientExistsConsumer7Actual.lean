import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QFullTargetUnitPairConsumerActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullTargetUnitPairConsumerActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer7Actual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

structure S3127G2FreeQuotientExistsConsumer7  : Type 2 where
  data : S3127G2QFullTargetUnitPairConsumer A act hfree hInv
  target : S3127FreeQuotientTarget A G
  target_eq : target = data.pair.target

noncomputable def S3127G2FreeQuotientExistsConsumer7.of :
    S3127G2FreeQuotientExistsConsumer7 A act hfree hInv := by
  let D := S3127G2QFullTargetUnitPairConsumer.of A act hfree hInv
  exact { data := D, target := D.pair.target, target_eq := rfl }

theorem S3127G2FreeQuotientExistsConsumer7_invariant (g : G) :
    S3127G2Action A act g ≫
      (S3127G2FreeQuotientExistsConsumer7.of A act hfree hInv).data.quotientMap =
      (S3127G2FreeQuotientExistsConsumer7.of A act hfree hInv).data.quotientMap :=
  S3127G2QFullTargetUnitPairConsumer_invariant A act hfree hInv g

#check S3127G2FreeQuotientExistsConsumer7
#check S3127G2FreeQuotientExistsConsumer7.of
#check S3127G2FreeQuotientExistsConsumer7_invariant
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer7Actual
end

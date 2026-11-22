import tmp.sheaf.xif.paper.S3127G2QFullTargetUnitPairActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullTargetUnitPairActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QFullTargetUnitPairConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

structure S3127G2QFullTargetUnitPairConsumer  : Type 2 where
  pair : S3127G2QFullTargetUnitPair A act hfree hInv
  quotientMap : A ⟶ pair.target.quotientObj
  quotientMap_eq : HEq quotientMap pair.target.quotientMap

noncomputable def S3127G2QFullTargetUnitPairConsumer.of :
    S3127G2QFullTargetUnitPairConsumer A act hfree hInv := by
  let P := S3127G2QFullTargetUnitPair.of A act hfree hInv
  exact { pair := P, quotientMap := P.target.quotientMap, quotientMap_eq := HEq.rfl }

theorem S3127G2QFullTargetUnitPairConsumer_invariant (g : G) :
    S3127G2Action A act g ≫
      (S3127G2QFullTargetUnitPairConsumer.of A act hfree hInv).quotientMap =
      (S3127G2QFullTargetUnitPairConsumer.of A act hfree hInv).quotientMap := by
  change S3127G2Action A act g ≫
      (S3127G2QFullTargetUnitPair.of A act hfree hInv).target.quotientMap =
    (S3127G2QFullTargetUnitPair.of A act hfree hInv).target.quotientMap
  exact (S3127G2QFullTargetUnitPair.of A act hfree hInv).target.invariant g

#check S3127G2QFullTargetUnitPairConsumer
#check S3127G2QFullTargetUnitPairConsumer.of
#check S3127G2QFullTargetUnitPairConsumer_invariant
end LeanFormal.IUT.XiFPaper.S3127G2QFullTargetUnitPairConsumerActual
end

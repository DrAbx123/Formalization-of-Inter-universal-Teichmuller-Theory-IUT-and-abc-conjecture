import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer5Actual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer5Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer6Actual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)
variable (D : S3127G2FreeQuotientExistsConsumer5 A act hfree hInv)

structure S3127G2FreeQuotientExistsConsumer6  : Type 2 where
  data : S3127G2FreeQuotientExistsConsumer5 A act hfree hInv
  target : S3127FreeQuotientTarget A G
  target_eq : target = data.target
  quotientMap : A ⟶ target.quotientObj
  quotientMap_eq : HEq quotientMap data.target.quotientMap

noncomputable def S3127G2FreeQuotientExistsConsumer6.of :
    S3127G2FreeQuotientExistsConsumer6 A act hfree hInv := by
  let D := S3127G2FreeQuotientExistsConsumer5.of A act hfree hInv
  exact {
    data := D
    target := D.target
    target_eq := rfl
    quotientMap := D.target.quotientMap
    quotientMap_eq := HEq.rfl }

theorem S3127G2FreeQuotientExistsConsumer6_invariant (g : G) :
    S3127G2Action A act g ≫
      (S3127G2FreeQuotientExistsConsumer6.of A act hfree hInv).quotientMap =
      (S3127G2FreeQuotientExistsConsumer6.of A act hfree hInv).quotientMap := by
  change S3127G2Action A act g ≫
      (S3127G2FreeQuotientExistsConsumer5.of A act hfree hInv).target.quotientMap =
    (S3127G2FreeQuotientExistsConsumer5.of A act hfree hInv).target.quotientMap
  exact (S3127G2FreeQuotientExistsConsumer5.of A act hfree hInv).target.invariant g

#check S3127G2FreeQuotientExistsConsumer6
#check S3127G2FreeQuotientExistsConsumer6.of
#check S3127G2FreeQuotientExistsConsumer6_invariant
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer6Actual
end

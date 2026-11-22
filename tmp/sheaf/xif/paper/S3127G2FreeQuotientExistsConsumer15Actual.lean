import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer14Actual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer13Actual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer14Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer13Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer15Actual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

structure S3127G2FreeQuotientExistsConsumer15
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    [Fintype G] [DecidableEq G]
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1)
    (hInv : ∀ g : G,
      S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act) :
    Type 2 where
  target : S3127FreeQuotientTarget A G
  quotientMap : A ⟶ target.quotientObj
  invariant : ∀ g : G, S3127G2Action A act g ≫ quotientMap = quotientMap

noncomputable def S3127G2FreeQuotientExistsConsumer15.of :
    S3127G2FreeQuotientExistsConsumer15 A act hfree hInv := by
  let T := S3127G2FreeQuotientExistsConsumer13_target A act hfree hInv
  exact {
    target := T
    quotientMap := T.quotientMap
    invariant := fun g => T.invariant g }

#check S3127G2FreeQuotientExistsConsumer15
#check S3127G2FreeQuotientExistsConsumer15.of
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer15Actual
end

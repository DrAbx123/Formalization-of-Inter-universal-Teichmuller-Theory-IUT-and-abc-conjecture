import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer9Actual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer8Actual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer9Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer8Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer10Actual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

theorem S3127G2FreeQuotientExistsConsumer10_exists
    (act : S3127OverRAction A G)
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1)
    (hInv : ∀ g : G,
      S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act) :
    ∃ T : S3127FreeQuotientTarget A G,
      T.quotientObj = S3127G2FreeQuotientExistsConsumer8_quotientObj
        A act hfree hInv :=
  S3127G2FreeQuotientExistsConsumer9_exists A act hfree hInv

theorem S3127G2FreeQuotientExistsConsumer10_target_quotientObj
    (act : S3127OverRAction A G)
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1)
    (hInv : ∀ g : G,
      S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act) :
    (S3127G2FreeQuotientExistsConsumer9_target A act hfree hInv).quotientObj =
      S3127G2FreeQuotientExistsConsumer8_quotientObj A act hfree hInv :=
  S3127G2FreeQuotientExistsConsumer9_quotientObj_eq A act hfree hInv

#check S3127G2FreeQuotientExistsConsumer10_exists
#check S3127G2FreeQuotientExistsConsumer10_target_quotientObj
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer10Actual
end

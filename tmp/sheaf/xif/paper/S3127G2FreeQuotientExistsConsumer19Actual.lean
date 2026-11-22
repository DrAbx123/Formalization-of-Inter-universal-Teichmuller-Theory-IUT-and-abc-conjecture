import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer18Actual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer17Actual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer8Actual
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
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer18Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer17Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer8Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer13Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer19Actual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

theorem S3127G2FreeQuotientExistsConsumer19_exists_and_quotientObj :
    (∃ T : S3127FreeQuotientTarget A G,
      T = S3127G2FreeQuotientExistsConsumer17_target A act hfree hInv) ∧
    (S3127G2FreeQuotientExistsConsumer17_target A act hfree hInv).quotientObj =
      S3127G2FreeQuotientExistsConsumer8_quotientObj A act hfree hInv :=
  ⟨S3127G2FreeQuotientExistsConsumer18_target_exists A act hfree hInv,
    S3127G2FreeQuotientExistsConsumer13_quotientObj_eq A act hfree hInv⟩

#check S3127G2FreeQuotientExistsConsumer19_exists_and_quotientObj
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer19Actual
end

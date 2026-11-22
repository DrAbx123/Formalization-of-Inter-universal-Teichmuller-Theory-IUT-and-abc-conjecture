import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer11Actual
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
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer11Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer8Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer12Actual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

structure S3127G2FreeQuotientExistsConsumer12  : Type 2 where
  target : S3127FreeQuotientTarget A G
  quotientObj_eq : target.quotientObj =
    S3127G2FreeQuotientExistsConsumer8_quotientObj A act hfree hInv
  existsShape : ∃ T : S3127FreeQuotientTarget A G,
    T.quotientObj = S3127G2FreeQuotientExistsConsumer8_quotientObj
      A act hfree hInv

noncomputable def S3127G2FreeQuotientExistsConsumer12.of :
    S3127G2FreeQuotientExistsConsumer12 A act hfree hInv where
  target := S3127G2FreeQuotientExistsConsumer9_target A act hfree hInv
  quotientObj_eq := S3127G2FreeQuotientExistsConsumer9_quotientObj_eq A act hfree hInv
  existsShape := S3127G2FreeQuotientExistsConsumer11_exists A act hfree hInv

theorem S3127G2FreeQuotientExistsConsumer12_exists :
    ∃ T : S3127FreeQuotientTarget A G,
      T.quotientObj = S3127G2FreeQuotientExistsConsumer8_quotientObj
        A act hfree hInv :=
  (S3127G2FreeQuotientExistsConsumer12.of A act hfree hInv).existsShape

#check S3127G2FreeQuotientExistsConsumer12
#check S3127G2FreeQuotientExistsConsumer12.of
#check S3127G2FreeQuotientExistsConsumer12_exists
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer12Actual
end

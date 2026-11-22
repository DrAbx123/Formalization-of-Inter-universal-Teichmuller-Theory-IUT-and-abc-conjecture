import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer22Actual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer21Actual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer20Actual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer22Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer21Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer20Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer23Actual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable (A : S3127FiniteEtaleOverKFull l)


noncomputable def S3127G2FreeQuotientExistsConsumer23_quotientMap
    (D : @S3127G2FreeQuotientExistsInput l G _ _ _ A) :
    A ⟶ S3127G2FreeQuotientExistsConsumer22_quotientObj A D :=
  (S3127G2FreeQuotientExistsConsumer21_target A D).quotientMap

theorem S3127G2FreeQuotientExistsConsumer23_invariant
    (D : @S3127G2FreeQuotientExistsInput l G _ _ _ A) (g : G) :
    S3127G2Action A D.act g ≫
      S3127G2FreeQuotientExistsConsumer23_quotientMap A D =
      S3127G2FreeQuotientExistsConsumer23_quotientMap A D :=
  (S3127G2FreeQuotientExistsConsumer21_target A D).invariant g

#check S3127G2FreeQuotientExistsConsumer23_quotientMap
#check S3127G2FreeQuotientExistsConsumer23_invariant
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer23Actual
end

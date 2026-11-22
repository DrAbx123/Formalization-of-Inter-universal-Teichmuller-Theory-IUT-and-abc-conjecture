import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
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
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer21Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer20Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer22Actual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable (A : S3127FiniteEtaleOverKFull l)


noncomputable def S3127G2FreeQuotientExistsConsumer22_quotientObj
    (D : @S3127G2FreeQuotientExistsInput l G _ _ _ A) :
    S3127FiniteEtaleOverKFull l :=
  (S3127G2FreeQuotientExistsConsumer21_target A D).quotientObj

theorem S3127G2FreeQuotientExistsConsumer22_exists
    (D : @S3127G2FreeQuotientExistsInput l G _ _ _ A) :
    ∃ T : S3127FreeQuotientTarget A G, S3127QuotientUniversal T :=
  S3127G2FreeQuotientExistsConsumer21_exists A D

#check S3127G2FreeQuotientExistsConsumer22_quotientObj
#check S3127G2FreeQuotientExistsConsumer22_exists
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer22Actual
end

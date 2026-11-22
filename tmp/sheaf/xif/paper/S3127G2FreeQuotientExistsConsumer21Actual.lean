import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer20Actual
import tmp.sheaf.xif.paper.S3127G2TargetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer20Actual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer21Actual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable (A : S3127FiniteEtaleOverKFull l)


noncomputable def S3127G2FreeQuotientExistsConsumer21_target
    (D : S3127G2FreeQuotientExistsInput (G := G) A) :
    S3127FreeQuotientTarget A G :=
  S3127FreeQuotientTargetOf A D.act D.hfree D.hInv

theorem S3127G2FreeQuotientExistsConsumer21_exists
    (D : S3127G2FreeQuotientExistsInput (G := G) A) :
    ∃ T : S3127FreeQuotientTarget A G, S3127QuotientUniversal T :=
  S3127G2FreeQuotientExistsConsumer20_exists A D

#check S3127G2FreeQuotientExistsConsumer21_target
#check S3127G2FreeQuotientExistsConsumer21_exists
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer21Actual
end

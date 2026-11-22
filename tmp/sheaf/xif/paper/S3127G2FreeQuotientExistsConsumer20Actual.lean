import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer15Actual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumerActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataConsumer2Actual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataConsumer2Actual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumerActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer20Actual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable (A : S3127FiniteEtaleOverKFull l)

/-- Exact remaining input for `S3127FreeQuotientExists`: an action with
free/invariant data plus explicit universal data. -/
structure S3127G2FreeQuotientExistsInput : Type 2 where
  act : S3127OverRAction A G
  hfree : ∀ (x : A.obj.left.left) (g : G),
    (S3127G2Action A act g).hom.left.left x = x → g = 1
  hInv : ∀ g : G,
    S3127G2Action A act g ≫ S3127G2QuotientMap A act =
      S3127G2QuotientMap A act
  data : S3127G2UniversalData (A := A) (T := S3127FreeQuotientTargetOf A act hfree hInv)

theorem S3127G2FreeQuotientExistsConsumer20_exists
    (D : S3127G2FreeQuotientExistsInput (G := G) A) :
    ∃ T : S3127FreeQuotientTarget A G, S3127QuotientUniversal T :=
  S3127G2FreeQuotientExistsConsumer_exists
    A D.act D.hfree D.hInv D.data

#check S3127G2FreeQuotientExistsInput
#check S3127G2FreeQuotientExistsConsumer20_exists
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer20Actual
end

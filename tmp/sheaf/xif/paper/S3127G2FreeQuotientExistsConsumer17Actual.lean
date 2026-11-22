import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer16Actual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer16Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer17Actual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

noncomputable def S3127G2FreeQuotientExistsConsumer17_target :
    S3127FreeQuotientTarget A G :=
  (S3127G2FreeQuotientExistsConsumer16_data A act hfree hInv).target

noncomputable def S3127G2FreeQuotientExistsConsumer17_quotientMap :
    A ⟶ (S3127G2FreeQuotientExistsConsumer17_target A act hfree hInv).quotientObj :=
  (S3127G2FreeQuotientExistsConsumer16_data A act hfree hInv).quotientMap

#check S3127G2FreeQuotientExistsConsumer17_target
#check S3127G2FreeQuotientExistsConsumer17_quotientMap
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer17Actual
end

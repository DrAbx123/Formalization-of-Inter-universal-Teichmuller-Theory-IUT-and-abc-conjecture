import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QFullConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

theorem S3127G2QFullConsumer_quotientObj :
    (S3127FreeQuotientTargetOf A act hfree hInv).quotientObj =
      S3127G2QuotientObj (S3127G2QFull A act) := rfl

theorem S3127G2QFullConsumer_quotientMap :
    (S3127FreeQuotientTargetOf A act hfree hInv).quotientMap =
      S3127G2QuotientMap A act := rfl

theorem S3127G2QFullConsumer_action :
    (S3127FreeQuotientTargetOf A act hfree hInv).action =
      S3127G2Action A act := rfl

#check S3127G2QFullConsumer_quotientObj
#check S3127G2QFullConsumer_quotientMap
#check S3127G2QFullConsumer_action
end LeanFormal.IUT.XiFPaper.S3127G2QFullConsumerActual
end

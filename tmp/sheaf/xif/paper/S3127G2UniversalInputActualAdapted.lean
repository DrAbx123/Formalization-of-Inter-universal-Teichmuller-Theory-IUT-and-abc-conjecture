import tmp.sheaf.xif.paper.S3127G2TargetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalInputActualAdapted
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

structure S3127G2UniversalInput : Type where
  target : S3127FreeQuotientTarget A G
  target_action : target.action = S3127G2Action A act
  target_quotientMap : target.quotientMap = S3127G2QuotientMap A act

noncomputable def S3127G2UniversalInput.of : S3127G2UniversalInput A act hfree hInv where
  target := S3127FreeQuotientTargetOf A act hfree hInv
  target_action := rfl
  target_quotientMap := rfl

#check S3127G2UniversalInput
#check S3127G2UniversalInput.of
end LeanFormal.IUT.XiFPaper.S3127G2UniversalInputActualAdapted
end

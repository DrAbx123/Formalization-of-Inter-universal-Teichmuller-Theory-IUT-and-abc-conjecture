import tmp.sheaf.xif.paper.S3127G2TargetUnitActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2TargetUnitDataActual
variable {l : PrimeGeFive} {G : Type} [Group G]
structure S3127G2TargetUnitData
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    [Fintype G] [DecidableEq G]
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1)
    (hInv : ∀ g : G,
      S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act) : Type 2 where
  target : S3127FreeQuotientTarget A G
  target_eq : target = S3127FreeQuotientTargetUnit A act hfree hInv

noncomputable def S3127G2TargetUnitData.of
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    [Fintype G] [DecidableEq G]
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1)
    (hInv : ∀ g : G,
      S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act) :
    S3127G2TargetUnitData A act hfree hInv where
  target := S3127FreeQuotientTargetUnit A act hfree hInv
  target_eq := rfl

#check S3127G2TargetUnitData
#check S3127G2TargetUnitData.of
end LeanFormal.IUT.XiFPaper.S3127G2TargetUnitDataActual
end

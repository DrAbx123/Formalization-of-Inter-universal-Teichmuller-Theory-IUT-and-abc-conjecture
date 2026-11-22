import tmp.sheaf.xif.paper.S3127G2QFullUnitActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
import tmp.sheaf.xif.paper.S3127GammaActionActual
import tmp.sheaf.xif.paper.S3127GammaCompActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127GammaCompActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActual
namespace LeanFormal.IUT.XiFPaper.S3127G2TargetUnitActual
variable {l : PrimeGeFive} {G : Type} [Group G]

noncomputable def S3127FreeQuotientTargetUnit
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    [Fintype G] [DecidableEq G]
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1)
    (hInv : ∀ g : G, S3127G2Action A act g ≫ S3127G2QuotientMap A act =
      S3127G2QuotientMap A act) :
    S3127FreeQuotientTarget A G where
  action := S3127G2Action A act
  action_one := S3127G2Action_one A act
  action_mul := S3127G2Action_mul A act
  free := hfree
  quotientObj := S3127G2QuotientObj (S3127G2QFullUnit A act)
  quotientMap := S3127G2QuotientMap A act
  invariant := hInv

#check S3127FreeQuotientTargetUnit
end LeanFormal.IUT.XiFPaper.S3127G2TargetUnitActual
end

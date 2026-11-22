import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
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
namespace LeanFormal.IUT.XiFPaper.S3127G2TargetActual
variable {l : PrimeGeFive} {G : Type} [Group G]

noncomputable def S3127G2QFull
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    [Fintype G] : FiniteEtaleCover (S1419AffineScheme l) := by
  classical
  let R := S1348CoordinateRing l
  let Y := A.obj.left.left
  let hom := A.obj.hom.left
  letI := gammaAlgebraOf Y hom
  letI := gammaMulSemiringAction act.act
  letI := S3127GammaSMulCommClassOf A act
  letI : Algebra.Etale R (Scheme.Γ.obj (Opposite.op Y)) := gammaEtaleOf Y hom A.property.2 (by rfl)
  letI : Module.Finite R (Scheme.Γ.obj (Opposite.op Y)) := gammaFiniteOf Y hom A.property.1 (by rfl)
  exact affineQuotientCoverGeneral (R := R) (Scheme.Γ.obj (Opposite.op Y)) G

noncomputable def S3127FreeQuotientTargetOf
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
  quotientObj := S3127G2QuotientObj (S3127G2QFull A act)
  quotientMap := S3127G2QuotientMap A act
  invariant := hInv

#check S3127G2QFull
#check S3127FreeQuotientTargetOf
end LeanFormal.IUT.XiFPaper.S3127G2TargetActual
end

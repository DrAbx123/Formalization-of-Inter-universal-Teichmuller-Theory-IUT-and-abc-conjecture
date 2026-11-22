import tmp.sheaf.xif.paper.S3127G2QFullUnitActual
import tmp.sheaf.xif.paper.S3127G2TargetUnitActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QFullTargetUnitPairActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

structure S3127G2QFullTargetUnitPair  : Type 2 where
  qfull : FiniteEtaleCover (S1419AffineScheme l)
  target : S3127FreeQuotientTarget A G
  qfull_eq : qfull = S3127G2QFullUnit A act
  target_eq : target = S3127FreeQuotientTargetUnit A act hfree hInv
  quotientObj_eq : target.quotientObj = S3127G2QuotientObj qfull

noncomputable def S3127G2QFullTargetUnitPair.of :
    S3127G2QFullTargetUnitPair A act hfree hInv where
  qfull := S3127G2QFullUnit A act
  target := S3127FreeQuotientTargetUnit A act hfree hInv
  qfull_eq := rfl
  target_eq := rfl
  quotientObj_eq := rfl

theorem S3127G2QFullTargetUnitPair_exact :
    (S3127G2QFullTargetUnitPair.of A act hfree hInv).target.quotientObj =
      S3127G2QuotientObj (S3127G2QFullUnit A act) :=
  (S3127G2QFullTargetUnitPair.of A act hfree hInv).quotientObj_eq

#check S3127G2QFullTargetUnitPair
#check S3127G2QFullTargetUnitPair.of
#check S3127G2QFullTargetUnitPair_exact
end LeanFormal.IUT.XiFPaper.S3127G2QFullTargetUnitPairActual
end

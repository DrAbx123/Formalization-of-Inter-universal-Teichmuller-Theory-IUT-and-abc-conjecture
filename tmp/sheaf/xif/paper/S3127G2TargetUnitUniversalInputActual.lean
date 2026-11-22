import tmp.sheaf.xif.paper.S3127G2TargetUnitActual
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2QFullUnitActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullUnitActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2TargetUnitUniversalInputActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

structure S3127G2TargetUnitUniversalInput  : Type 2 where
  target : S3127FreeQuotientTarget A G
  quotientObj : S3127FiniteEtaleOverKFull l
  quotientMap : A ⟶ quotientObj
  target_eq : target = S3127FreeQuotientTargetUnit A act hfree hInv
  quotientObj_eq : quotientObj = target.quotientObj
  quotientMap_eq : HEq quotientMap target.quotientMap

noncomputable def S3127G2TargetUnitUniversalInput.of :
    S3127G2TargetUnitUniversalInput A act hfree hInv where
  target := S3127FreeQuotientTargetUnit A act hfree hInv
  quotientObj := (S3127FreeQuotientTargetUnit A act hfree hInv).quotientObj
  quotientMap := (S3127FreeQuotientTargetUnit A act hfree hInv).quotientMap
  target_eq := rfl
  quotientObj_eq := rfl
  quotientMap_eq := HEq.rfl

#check S3127G2TargetUnitUniversalInput
#check S3127G2TargetUnitUniversalInput.of
end LeanFormal.IUT.XiFPaper.S3127G2TargetUnitUniversalInputActual
end

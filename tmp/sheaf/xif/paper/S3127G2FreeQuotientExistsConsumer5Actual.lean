import tmp.sheaf.xif.paper.S3127G2QFullUnitActual
import tmp.sheaf.xif.paper.S3127G2TargetUnitActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
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
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer5Actual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

structure S3127G2FreeQuotientExistsConsumer5  : Type 2 where
  target : S3127FreeQuotientTarget A G
  cover : FiniteEtaleCover (S1419AffineScheme l)
  target_eq : target = S3127FreeQuotientTargetUnit A act hfree hInv
  cover_eq : cover = S3127G2QFullUnit A act

noncomputable def S3127G2FreeQuotientExistsConsumer5.of :
    S3127G2FreeQuotientExistsConsumer5 A act hfree hInv where
  target := S3127FreeQuotientTargetUnit A act hfree hInv
  cover := S3127G2QFullUnit A act
  target_eq := rfl
  cover_eq := rfl

noncomputable def S3127G2FreeQuotientExistsConsumer5_quotientMap :
    A ⟶ (S3127G2FreeQuotientExistsConsumer5.of A act hfree hInv).target.quotientObj :=
  (S3127G2FreeQuotientExistsConsumer5.of A act hfree hInv).target.quotientMap

theorem S3127G2FreeQuotientExistsConsumer5_invariant (g : G) :
    S3127G2Action A act g ≫
      S3127G2FreeQuotientExistsConsumer5_quotientMap A act hfree hInv =
      S3127G2FreeQuotientExistsConsumer5_quotientMap A act hfree hInv :=
  (S3127G2FreeQuotientExistsConsumer5.of A act hfree hInv).target.invariant g

#check S3127G2FreeQuotientExistsConsumer5
#check S3127G2FreeQuotientExistsConsumer5.of
#check S3127G2FreeQuotientExistsConsumer5_invariant
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer5Actual
end

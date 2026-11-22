import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsFinalActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsFinalActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsInterfaceActual
variable {l : PrimeGeFive}

/-- Paper-level input range for G2: for every finite group `G` and full cover `A`,
a free `G`-action on `A` with universal quotient data. This is the exact
geometric/quotient input; it is NOT proved unconditionally here. -/
def S3127FreeQuotientPaperInput : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (A : S3127FiniteEtaleOverKFull l),
    ∃ (act : S3127OverRAction A G)
      (hfree : ∀ (x : A.obj.left.left) (g : G),
        (S3127G2Action A act g).hom.left.left x = x → g = 1)
      (hInv : ∀ g : G,
        S3127G2Action A act g ≫ S3127G2QuotientMap A act =
          S3127G2QuotientMap A act),
      Nonempty
        (S3127G2UniversalData A
          (S3127FreeQuotientTargetOf A act hfree hInv))

/-- Named interface: paper input implies the G2 finite-group quotient existence. -/
theorem S3127FreeQuotientExists_of_freeAction_and_universalData
    (h : S3127FreeQuotientPaperInput (l := l)) :
    S3127FreeQuotientExists (l := l) :=
  S3127G2FreeQuotientExists_final h

/-- Consumer-facing scope marker: only conditional on `PaperInput`. -/
theorem S3127FreeQuotientExists_conditional :
    S3127FreeQuotientPaperInput (l := l) → S3127FreeQuotientExists (l := l) :=
  S3127FreeQuotientExists_of_freeAction_and_universalData

#check S3127FreeQuotientPaperInput
#check S3127FreeQuotientExists_of_freeAction_and_universalData
#check S3127FreeQuotientExists_conditional
end LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsInterfaceActual
end
import tmp.sheaf.xif.paper.S3127FreeQuotientExistsInterfaceActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataConsumer2Actual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataConsumer2Actual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsInterfaceActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127FreeQuotientPaperInputConsumerActual
variable {l : PrimeGeFive}

/-- A concrete free-action + universal-data input for one cover `A` and group `G`. -/
structure S3127FreeQuotientPaperInputData
    (A : S3127FiniteEtaleOverKFull l) (G : Type) [Group G] [Fintype G] [DecidableEq G] where
  act : S3127OverRAction A G
  hfree : ∀ (x : A.obj.left.left) (g : G),
    (S3127G2Action A act g).hom.left.left x = x → g = 1
  hInv : ∀ g : G,
    S3127G2Action A act g ≫ S3127G2QuotientMap A act =
      S3127G2QuotientMap A act
  data : S3127G2UniversalData A
    (S3127FreeQuotientTargetOf A act hfree hInv)

/-- Package pointwise paper input data into the global paper input. -/
noncomputable def S3127FreeQuotientPaperInput_of_data
    (h : ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G]
      (A : S3127FiniteEtaleOverKFull l), Nonempty (S3127FreeQuotientPaperInputData A G)) :
    S3127FreeQuotientPaperInput (l := l) := by
  intro G _ _ _ A
  obtain ⟨D⟩ := h G A
  exact ⟨D.act, D.hfree, D.hInv, ⟨D.data⟩⟩

/-- The per-object input yields its quotient universal property. -/
theorem S3127FreeQuotientPaperInputData_universal
    {A : S3127FiniteEtaleOverKFull l} {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (D : S3127FreeQuotientPaperInputData A G) :
    ∃ T : S3127FreeQuotientTarget A G, S3127QuotientUniversal T :=
  ⟨S3127FreeQuotientTargetOf A D.act D.hfree D.hInv,
    S3127G2UniversalDataConsumer2_universal
      (S3127FreeQuotientTargetOf A D.act D.hfree D.hInv) D.data⟩

/-- Consumer: pointwise paper input data proves the G2 existence theorem. -/
theorem S3127FreeQuotientExists_of_paperInputData
    (h : ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G]
      (A : S3127FiniteEtaleOverKFull l), Nonempty (S3127FreeQuotientPaperInputData A G)) :
    S3127FreeQuotientExists (l := l) :=
  S3127FreeQuotientExists_of_freeAction_and_universalData
    (S3127FreeQuotientPaperInput_of_data h)

#check S3127FreeQuotientPaperInputData
#check S3127FreeQuotientPaperInputData_universal
#check S3127FreeQuotientExists_of_paperInputData
end LeanFormal.IUT.XiFPaper.S3127FreeQuotientPaperInputConsumerActual
end
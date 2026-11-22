import tmp.sheaf.xif.paper.S3127G2UniversalDataConditionalActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
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
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataConditionalActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsOfData1Actual
variable {l : PrimeGeFive}

theorem S3127FreeQuotientExists_of_data
    (h : ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G]
      (A : S3127FiniteEtaleOverKFull l),
      ∃ (act : S3127OverRAction A G)
        (hfree : ∀ (x : A.obj.left.left) (g : G),
          (S3127G2Action A act g).hom.left.left x = x → g = 1)
        (hInv : ∀ g : G,
          S3127G2Action A act g ≫ S3127G2QuotientMap A act =
            S3127G2QuotientMap A act),
        Nonempty
          (S3127G2UniversalData A
            (S3127FreeQuotientTargetOf A act hfree hInv))) :
    S3127FreeQuotientExists (l := l) := by
  intro G _ _ A
  classical
  rcases h G A with ⟨act, hfree, hInv, ⟨D⟩⟩
  exact S3127G2UniversalDataConditional_exists A act hfree hInv D

#check S3127FreeQuotientExists_of_data
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsOfData1Actual
end

import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataOfHfacActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataConsumer2Actual
noncomputable section
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
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
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfHfacActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsOfFreeActionActual
variable {l : PrimeGeFive} {G : Type} [Group G]

/-- Per-action G2 theorem: given a free finite-group action with invariant quotient map
and the raw lifting property `hfac`, the canonical target has the universal property.
This is the final per-action shape; it does not use the global `PaperInput` hypothesis. -/
theorem S3127FreeQuotientExists_ofFreeAction
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    [Fintype G] [DecidableEq G]
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1)
    (hInv : ∀ g : G,
      S3127G2Action A act g ≫ S3127G2QuotientMap A act =
        S3127G2QuotientMap A act)
    (hfac : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
      (_hinv : ∀ g : G, S3127G2Action A act g ≫ f = f),
      ∃! v_raw :
        S3127FullForget.obj (S3127G2QuotientObj (S3127G2QFull A act)) ⟶
          S3127FullForget.obj B,
        S3127FullForget.map (S3127G2QuotientMap A act) ≫ v_raw =
          S3127FullForget.map f) :
    ∃ T : S3127FreeQuotientTarget A G, S3127QuotientUniversal T :=
  ⟨S3127FreeQuotientTargetOf A act hfree hInv,
    S3127G2UniversalDataConsumer2_universal
      (S3127FreeQuotientTargetOf A act hfree hInv)
      (S3127G2UniversalData_of_hfac A act hfree hInv hfac)⟩

#check S3127FreeQuotientExists_ofFreeAction
end LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsOfFreeActionActual
end
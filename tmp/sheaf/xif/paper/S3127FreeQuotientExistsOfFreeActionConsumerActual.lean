import tmp.sheaf.xif.paper.S3127FreeQuotientExistsOfFreeActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfHfacActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataConsumer2Actual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsOfFreeActionActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsOfFreeActionConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G]

/-- Promotion: the universal property holds directly for the canonical target. -/
theorem S3127FreeQuotientTargetOf_universal_of_hfac
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
    S3127QuotientUniversal
      (S3127FreeQuotientTargetOf A act hfree hInv) :=
  S3127G2UniversalDataConsumer2_universal
    (S3127FreeQuotientTargetOf A act hfree hInv)
    (S3127G2UniversalData_of_hfac A act hfree hInv hfac)

/-- Consumer: the per-action theorem gives the canonical target directly. -/
theorem S3127FreeQuotientExists_ofFreeAction_target
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
    S3127QuotientUniversal
      (S3127FreeQuotientTargetOf A act hfree hInv) :=
  S3127FreeQuotientTargetOf_universal_of_hfac A act hfree hInv hfac

#check S3127FreeQuotientTargetOf_universal_of_hfac
#check S3127FreeQuotientExists_ofFreeAction_target
end LeanFormal.IUT.XiFPaper.S3127FreeQuotientExistsOfFreeActionConsumerActual
end
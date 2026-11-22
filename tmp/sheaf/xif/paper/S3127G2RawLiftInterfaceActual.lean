import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataOfHfacActual
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
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfHfacActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2RawLiftInterfaceActual
variable {l : PrimeGeFive} {G : Type} [Group G]

/-- Exact raw-lift data still to be produced (RawFac + uniqueness): a lift for
every invariant map, its factorization, and its uniqueness. -/
structure S3127G2RawLiftData
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) [Fintype G] [DecidableEq G]
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1)
    (hInv : ∀ g : G,
      S3127G2Action A act g ≫ S3127G2QuotientMap A act =
        S3127G2QuotientMap A act) where
  lift : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (_hinv : ∀ g : G, S3127G2Action A act g ≫ f = f),
    S3127FullForget.obj (S3127G2QuotientObj (S3127G2QFull A act)) ⟶
      S3127FullForget.obj B
  fac : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hinv : ∀ g : G, S3127G2Action A act g ≫ f = f),
    S3127FullForget.map (S3127G2QuotientMap A act) ≫ lift f hinv =
      S3127FullForget.map f
  uniq : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hinv : ∀ g : G, S3127G2Action A act g ≫ f = f)
    (v_raw : S3127FullForget.obj (S3127G2QuotientObj (S3127G2QFull A act)) ⟶
      S3127FullForget.obj B),
    S3127FullForget.map (S3127G2QuotientMap A act) ≫ v_raw =
      S3127FullForget.map f →
    v_raw = lift f hinv

/-- Turn raw-lift data into the `hfac` existential-unique form. -/
noncomputable def S3127G2RawLiftData.toHfac
    {A : S3127FiniteEtaleOverKFull l} {act : S3127OverRAction A G} [Fintype G] [DecidableEq G]
    {hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1}
    {hInv : ∀ g : G,
      S3127G2Action A act g ≫ S3127G2QuotientMap A act =
        S3127G2QuotientMap A act}
    (D : S3127G2RawLiftData A act hfree hInv) :
    ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
      (_hinv : ∀ g : G, S3127G2Action A act g ≫ f = f),
      ∃! v_raw : S3127FullForget.obj (S3127G2QuotientObj (S3127G2QFull A act)) ⟶
        S3127FullForget.obj B,
        S3127FullForget.map (S3127G2QuotientMap A act) ≫ v_raw =
          S3127FullForget.map f :=
  fun f hinv => ⟨D.lift f hinv, D.fac f hinv, fun v hv => D.uniq f hinv v hv⟩

/-- Raw-lift data therefore yields universal data for the canonical target. -/
noncomputable def S3127G2UniversalData_of_rawLiftData
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) [Fintype G] [DecidableEq G]
    (hfree : ∀ (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x → g = 1)
    (hInv : ∀ g : G,
      S3127G2Action A act g ≫ S3127G2QuotientMap A act =
        S3127G2QuotientMap A act)
    (D : S3127G2RawLiftData A act hfree hInv) :
    S3127G2UniversalData A (S3127FreeQuotientTargetOf A act hfree hInv) :=
  S3127G2UniversalData_of_hfac A act hfree hInv D.toHfac

#check S3127G2RawLiftData
#check S3127G2RawLiftData.toHfac
#check S3127G2UniversalData_of_rawLiftData
end LeanFormal.IUT.XiFPaper.S3127G2RawLiftInterfaceActual
end
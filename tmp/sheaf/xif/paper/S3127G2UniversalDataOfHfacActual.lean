import tmp.sheaf.xif.paper.S3127G2UniversalTargetActual
import tmp.sheaf.xif.paper.S3127G2UniversalParamActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2QuotientObjActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
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
open LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalParamActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfHfacActual
variable {l : PrimeGeFive} {G : Type} [Group G]

/-- Bridge: explicit raw lifting property (hfac) yields universal data for the
canonical target. This is the direct landing point once RawFac is solved. -/
noncomputable def S3127G2UniversalData_of_hfac
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) [Fintype G] [DecidableEq G]
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
    S3127G2UniversalData A
      (S3127FreeQuotientTargetOf A act hfree hInv) :=
  let T := S3127FreeQuotientTargetOf A act hfree hInv
  S3127G2UniversalData.ofUniversal (A := A) (T := T)
    (S3127G2Universal_of_phi
      (A := A) (act := act)
      (Qobj := T.quotientObj) (q := T.quotientMap)
      (phi := fun _ _ => True)
      (hphi := fun _ _ => trivial)
      hfac)

#check S3127G2UniversalData_of_hfac
end LeanFormal.IUT.XiFPaper.S3127G2UniversalDataOfHfacActual
end
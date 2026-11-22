import tmp.sheaf.xif.paper.S3127G2UniversalParamActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalParamActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2RawFacConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable (A : S3127FiniteEtaleOverKFull l)
variable (act : S3127OverRAction A G)
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

theorem S3127G2NonemptyUniversalData_of_rawFac
    (hfac : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
      (hf : ∀ g : G, S3127G2Action A act g ≫ f = f),
      ∃! v_raw : (S3127FullForget (l := l)).obj
          (S3127FreeQuotientTargetOf A act hfree hInv).quotientObj ⟶
        (S3127FullForget (l := l)).obj B,
        (S3127FullForget (l := l)).map
          (S3127FreeQuotientTargetOf A act hfree hInv).quotientMap ≫ v_raw =
          (S3127FullForget (l := l)).map f) :
    Nonempty (S3127G2UniversalData A
      (S3127FreeQuotientTargetOf A act hfree hInv)) :=
  let hq : S3127QuotientUniversal
      (S3127FreeQuotientTargetOf A act hfree hInv) :=
    S3127G2Universal_of_phi A act
      (S3127FreeQuotientTargetOf A act hfree hInv).quotientObj
      (S3127FreeQuotientTargetOf A act hfree hInv).quotientMap
      (fun _ _ => True) (fun _ _ => trivial) hfac
  ⟨S3127G2UniversalData.ofUniversal
    (T := S3127FreeQuotientTargetOf A act hfree hInv) hq⟩

#check S3127G2NonemptyUniversalData_of_rawFac
end LeanFormal.IUT.XiFPaper.S3127G2RawFacConsumerActual
end

import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsConsumer3Actual
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer3Actual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer4Actual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)
variable (P : S3127G2UniversalData (A := A) (T := S3127FreeQuotientTargetOf A act hfree hInv))

theorem S3127G2FreeQuotientExistsConsumer4_fac
    {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, S3127G2Action A act g ≫ f = f) :
    S3127G2FreeQuotientExistsConsumer3_quotientMap A act hfree hInv P ≫
      S3127G2UniversalData.lift P f hf = f :=
  S3127G2UniversalData.fac P f hf

theorem S3127G2FreeQuotientExistsConsumer4_existsUnique
    {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, S3127G2Action A act g ≫ f = f) :
    ∃! v : S3127G2FreeQuotientExistsConsumer3_quotientObj A act hfree hInv P ⟶ B,
      S3127G2FreeQuotientExistsConsumer3_quotientMap A act hfree hInv P ≫ v = f :=
  ⟨S3127G2UniversalData.lift P f hf, S3127G2UniversalData.fac P f hf, fun v hv => S3127G2UniversalData.uniq P f hf v hv⟩

#check S3127G2FreeQuotientExistsConsumer4_fac
#check S3127G2FreeQuotientExistsConsumer4_existsUnique
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumer4Actual
end

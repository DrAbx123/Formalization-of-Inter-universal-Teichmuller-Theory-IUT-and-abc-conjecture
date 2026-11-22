import tmp.sheaf.xif.paper.S3127G2FreeQuotientExistsOfDataActual
import tmp.sheaf.xif.paper.S3127G2UniversalDataConsumer2Actual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataConsumer2Actual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsOfDataActual
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumerActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

/-- Consumer of UniversalDataConsumer2 / FreeQuotientExistsOfData:
for fixed action/free/invariant data, explicit universal data yields the
local `∃ T, S3127QuotientUniversal T` shape. -/
noncomputable def S3127G2FreeQuotientExistsConsumer
    (P : S3127G2UniversalData (A := A) (T := S3127FreeQuotientTargetOf A act hfree hInv)) :
    Σ' T : S3127FreeQuotientTarget A G, S3127QuotientUniversal T :=
  S3127G2TargetWithUniversalOfData A act hfree hInv P

theorem S3127G2FreeQuotientExistsConsumer_exists
    (P : S3127G2UniversalData (A := A) (T := S3127FreeQuotientTargetOf A act hfree hInv)) :
    ∃ T : S3127FreeQuotientTarget A G,
      S3127QuotientUniversal T := by
  obtain ⟨T, hT⟩ := S3127G2FreeQuotientExistsConsumer A act hfree hInv P
  exact ⟨T, hT⟩

theorem S3127G2FreeQuotientExistsConsumer_universal
    (P : S3127G2UniversalData (A := A) (T := S3127FreeQuotientTargetOf A act hfree hInv)) :
    S3127QuotientUniversal
      (S3127G2FreeQuotientExistsConsumer A act hfree hInv P).1 :=
  (S3127G2FreeQuotientExistsConsumer A act hfree hInv P).2

#check S3127G2FreeQuotientExistsConsumer
#check S3127G2FreeQuotientExistsConsumer_exists
#check S3127G2FreeQuotientExistsConsumer_universal
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsConsumerActual
end

import tmp.sheaf.xif.paper.S3127G2UniversalDataConsumer2Actual
import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2RActionActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
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
open LeanFormal.IUT.XiFPaper.S3127G2TargetActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsOfDataActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]
variable (hfree : ∀ (x : A.obj.left.left) (g : G),
  (S3127G2Action A act g).hom.left.left x = x → g = 1)
variable (hInv : ∀ g : G,
  S3127G2Action A act g ≫ S3127G2QuotientMap A act = S3127G2QuotientMap A act)

/-- Package a target together with the universal property derived from
explicit universal data.  This is the direct input shape of
`S3127FreeQuotientExists`. -/
noncomputable def S3127G2TargetWithUniversalOfData
    (P : S3127G2UniversalData (A := A) (T := S3127FreeQuotientTargetOf A act hfree hInv)) :
    Σ' T : S3127FreeQuotientTarget A G, S3127QuotientUniversal T :=
  ⟨S3127FreeQuotientTargetOf A act hfree hInv,
    S3127G2UniversalDataConsumer2_universal
      (S3127FreeQuotientTargetOf A act hfree hInv) P⟩

theorem S3127G2TargetWithUniversalOfData_universal
    (P : S3127G2UniversalData (A := A) (T := S3127FreeQuotientTargetOf A act hfree hInv)) :
    S3127QuotientUniversal
      (S3127G2TargetWithUniversalOfData A act hfree hInv P).1 :=
  (S3127G2TargetWithUniversalOfData A act hfree hInv P).2

#check S3127G2TargetWithUniversalOfData
#check S3127G2TargetWithUniversalOfData_universal
end LeanFormal.IUT.XiFPaper.S3127G2FreeQuotientExistsOfDataActual
end

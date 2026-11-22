import tmp.sheaf.xif.paper.S3127G2UniversalDataActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalDataConsumer2Actual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G]
variable {A : S3127FiniteEtaleOverKFull l} (T : S3127FreeQuotientTarget A G)


/-- Projection: explicit universal data yields the universal property. -/
noncomputable def S3127G2UniversalDataConsumer2_universal
    (P : S3127G2UniversalData A T) :
    S3127QuotientUniversal T :=
  S3127QuotientUniversal_of_data (A := A) (T := T) P

theorem S3127G2UniversalDataConsumer2_fac
    (P : S3127G2UniversalData A T)
    {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, T.action g ≫ f = f) :
    T.quotientMap ≫
      S3127G2UniversalData.lift P f hf = f :=
  S3127G2UniversalData.fac P f hf

theorem S3127G2UniversalDataConsumer2_uniq
    (P : S3127G2UniversalData A T)
    {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, T.action g ≫ f = f)
    (v : T.quotientObj ⟶ B) (hv : T.quotientMap ≫ v = f) :
    v = S3127G2UniversalData.lift P f hf :=
  S3127G2UniversalData.uniq P f hf v hv

theorem S3127G2UniversalDataConsumer2_existsUnique
    (P : S3127G2UniversalData A T)
    {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, T.action g ≫ f = f) :
    ∃! v : T.quotientObj ⟶ B, T.quotientMap ≫ v = f :=
  ⟨S3127G2UniversalData.lift P f hf,
    S3127G2UniversalData.fac P f hf,
    by intro v hv; exact S3127G2UniversalData.uniq P f hf v hv⟩

#check S3127G2UniversalDataConsumer2_universal
#check S3127G2UniversalDataConsumer2_fac
#check S3127G2UniversalDataConsumer2_uniq
#check S3127G2UniversalDataConsumer2_existsUnique
end LeanFormal.IUT.XiFPaper.S3127G2UniversalDataConsumer2Actual
end

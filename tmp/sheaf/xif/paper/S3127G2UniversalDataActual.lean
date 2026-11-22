import tmp.sheaf.xif.paper.S3127G2TargetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
variable {l : PrimeGeFive} {G : Type} [Group G] [Fintype G]
variable {A : S3127FiniteEtaleOverKFull l} (T : S3127FreeQuotientTarget A G)

/-- Explicit universal data: lift, factorization and uniqueness. -/
structure S3127G2UniversalData
    (A : S3127FiniteEtaleOverKFull l)
    (T : S3127FreeQuotientTarget A G) : Type 2 where
  lift : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B),
    (∀ g : G, T.action g ≫ f = f) → (T.quotientObj ⟶ B)
  fac : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, T.action g ≫ f = f),
    T.quotientMap ≫ lift f hf = f
  uniq : ∀ {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
    (hf : ∀ g : G, T.action g ≫ f = f) (v : (T.quotientObj ⟶ B)),
    T.quotientMap ≫ v = f → v = lift f hf

theorem S3127QuotientUniversal_of_data
    (P : S3127G2UniversalData A T) : S3127QuotientUniversal T := by
  intro B f hf
  exact ⟨S3127G2UniversalData.lift P f hf, S3127G2UniversalData.fac P f hf, fun v hv => S3127G2UniversalData.uniq P f hf v hv⟩

noncomputable def S3127G2UniversalData.ofUniversal
    (h : S3127QuotientUniversal T) : S3127G2UniversalData A T :=
  { lift := fun f hf => (h f hf).choose
    fac := fun f hf => (h f hf).choose_spec.1
    uniq := fun f hf v hv => (h f hf).choose_spec.2 v hv }

theorem S3127QuotientUniversal_iff_nonempty_data :
    S3127QuotientUniversal T ↔ Nonempty (S3127G2UniversalData A T) := by
  constructor
  · intro h
    exact ⟨S3127G2UniversalData.ofUniversal (A := A) (T := T) h⟩
  · rintro ⟨P⟩
    exact S3127QuotientUniversal_of_data (A := A) (T := T) P

#check S3127QuotientUniversal_of_data
#check S3127G2UniversalData.ofUniversal
#check S3127QuotientUniversal_iff_nonempty_data
end LeanFormal.IUT.XiFPaper.S3127G2UniversalDataActual
end

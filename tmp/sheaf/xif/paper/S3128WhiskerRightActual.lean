import Mathlib.CategoryTheory.Whiskering
open CategoryTheory
open CategoryTheory.Functor
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S3128WhiskerRightActual
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {C : Type u₁} [Category.{v₁, u₁} C]
variable {D : Type u₂} [Category.{v₂, u₂} D]
variable {E : Type u₃} [Category.{v₃, u₃} E]

noncomputable def S3128WhiskerRightIso
    {F G : C ⥤ D} (e : F ≅ G) (K : D ⥤ E) :
    F ⋙ K ≅ G ⋙ K :=
  isoWhiskerRight e K

theorem S3128WhiskerRightIso_refl
    (F : C ⥤ D) (K : D ⥤ E) :
    S3128WhiskerRightIso (Iso.refl F) K =
      Iso.refl (F ⋙ K) :=
  isoWhiskerRight_refl F K

theorem S3128WhiskerRightIso_trans
    {F G H : C ⥤ D} (e : F ≅ G) (f : G ≅ H)
    (K : D ⥤ E) :
    S3128WhiskerRightIso (e ≪≫ f) K =
      S3128WhiskerRightIso e K ≪≫
        S3128WhiskerRightIso f K :=
  isoWhiskerRight_trans e f K

#check S3128WhiskerRightIso
#check S3128WhiskerRightIso_refl
#check S3128WhiskerRightIso_trans
end LeanFormal.IUT.XiFPaper.S3128WhiskerRightActual
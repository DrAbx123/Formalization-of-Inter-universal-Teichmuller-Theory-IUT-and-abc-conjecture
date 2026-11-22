import tmp.sheaf.xif.paper.S3128PrestackActual
import tmp.sheaf.xif.paper.S3128OfHMapActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S3128FiberTypeActual
open LeanFormal.IUT.XiFPaper.S3128PrestackActual
open LeanFormal.IUT.XiFPaper.S3128OfHMapActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S3128OfHHelpersActual
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {C : Type u₁} [Category.{v₁, u₁} C]
variable {D : Type u₂} [Category.{v₂, u₂} D]
variable {E : Type u₃} [Category.{v₃, u₃} E]

theorem S3128WhiskerLeftIso_refl
    (F : C ⥤ D) (G : D ⥤ E) :
    S3128WhiskerLeftIso F (Iso.refl G) =
      Iso.refl (F ⋙ G) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp [S3128WhiskerLeftIso, Functor.whiskerLeft_app]

variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}
variable (H : Over U ⥤ Over U)
variable (hH : ∀ V : (Over U)ᵒᵖ, H.op.obj V ≅ V)

theorem S3128OfHHMap_mapIso_refl
    (V : (Over U)ᵒᵖ)
    (Y : S3128FiberType (X := X) (S3128L (H.op.obj V))) :
    (S3128OfHHMap H hH V).mapIso (Iso.refl Y) =
      Iso.refl ((S3128OfHHMap H hH V).obj Y) := by
  simp [Functor.mapIso_refl]

theorem S3128OfHHMap_mapIso_trans
    (V : (Over U)ᵒᵖ)
    {Y Z W : S3128FiberType (X := X) (S3128L (H.op.obj V))}
    (e : Y ≅ Z) (f : Z ≅ W) :
    (S3128OfHHMap H hH V).mapIso (e ≪≫ f) =
      (S3128OfHHMap H hH V).mapIso e
        ≪≫ (S3128OfHHMap H hH V).mapIso f := by
  simp [Functor.mapIso_trans]

#check S3128WhiskerLeftIso_refl
#check S3128OfHHMap_mapIso_refl
#check S3128OfHHMap_mapIso_trans
end LeanFormal.IUT.XiFPaper.S3128OfHHelpersActual
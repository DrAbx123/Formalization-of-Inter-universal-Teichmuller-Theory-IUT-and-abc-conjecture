import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Limits
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3129ProbeEtaleCoprod5
set_option maxHeartbeats 2000000
instance test {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f] [Etale g] : Etale (coprod.desc f g) := by
  let F : ULift.{0} WalkingPair → Scheme.{0} := fun i => i.1.casesOn X Y
  let h : ∀ i, F i ⟶ Z := fun i => by
    rcases i with ⟨j⟩
    cases j
    · exact f
    · exact g
  have hSigma : Etale (Sigma.desc h) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun i => by
      rcases i with ⟨j⟩
      cases j
      · exact inferInstance
      · exact inferInstance)
  have e : Arrow.mk (coprod.desc f g) ≅ Arrow.mk (Sigma.desc h) := by
    refine Arrow.isoMk (coprodIsoSigma X Y) (Iso.refl Z) ?_
    apply coprod.hom_ext
    · simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Iso.refl_hom,
        Category.id_comp]
      conv_lhs => rw [← ι_left_coprodIsoSigma_inv (X := X) (Y := Y)]
      have hcomp : (Sigma.ι F ⟨WalkingPair.left⟩ ≫ (coprodIsoSigma X Y).inv) ≫
          (coprodIsoSigma X Y).hom =
          Sigma.ι F ⟨WalkingPair.left⟩ := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change (Sigma.ι F ⟨WalkingPair.left⟩ ≫ (coprodIsoSigma X Y).inv) ≫
        (coprodIsoSigma X Y).hom ≫ Sigma.desc h =
        coprod.inl ≫ coprod.desc f g ≫ 𝟙 Z
      rw [← Category.assoc, hcomp, Sigma.ι_desc, Category.comp_id, coprod.inl_desc]
    · simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Iso.refl_hom,
        Category.id_comp]
      conv_lhs => rw [← ι_right_coprodIsoSigma_inv (X := X) (Y := Y)]
      have hcomp : (Sigma.ι F ⟨WalkingPair.right⟩ ≫ (coprodIsoSigma X Y).inv) ≫
          (coprodIsoSigma X Y).hom =
          Sigma.ι F ⟨WalkingPair.right⟩ := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change (Sigma.ι F ⟨WalkingPair.right⟩ ≫ (coprodIsoSigma X Y).inv) ≫
        (coprodIsoSigma X Y).hom ≫ Sigma.desc h =
        coprod.inr ≫ coprod.desc f g ≫ 𝟙 Z
      rw [← Category.assoc, hcomp, Sigma.ι_desc, Category.comp_id, coprod.inr_desc]
  exact (MorphismProperty.arrow_mk_iso_iff (P := @Etale) e).mpr hSigma
end LeanFormal.IUT.XiFPaper.S3129ProbeEtaleCoprod5
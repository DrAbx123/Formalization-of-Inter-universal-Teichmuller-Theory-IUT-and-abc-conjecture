import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Limits
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3129ProbeEtaleCoprod4
instance test {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f] [Etale g] : Etale (coprod.desc f g) := by
  let F : ULift.{0} WalkingPair → Scheme.{0} := fun i => i.1.casesOn X Y
  let h : ∀ i, F i ⟶ Z := fun i => i.1.casesOn f g
  have hSigma : Etale (Sigma.desc h) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun i => by
      cases i with
      | up j => cases j <;> infer_instance)
  have e : Arrow.mk (coprod.desc f g) ≅ Arrow.mk (Sigma.desc h) := by
    refine Arrow.isoMk (coprodIsoSigma X Y) (Iso.refl Z) ?_
    -- need (coprodIsoSigma).hom ≫ Sigma.desc h = coprod.desc f g
    ext1
    apply coprod.hom_ext
    · rw [Category.assoc]
      -- simplify left
      sorry
  exact (MorphismProperty.arrow_mk_iso_iff (P := @Etale) e).mpr hSigma
end LeanFormal.IUT.XiFPaper.S3129ProbeEtaleCoprod4
end
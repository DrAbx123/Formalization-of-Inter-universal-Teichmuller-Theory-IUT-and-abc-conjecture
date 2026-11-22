import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Limits
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3129ProbeEtaleCoprod3
instance test {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale f] [Etale g] : Etale (coprod.desc f g) := by
  refine IsZariskiLocalAtSource.of_openCover (P := @Etale)
    (f := coprod.desc f g) (𝒰 := coprodOpenCover.{0} X Y) ?_
  intro i
  cases i with
  | inl u =>
      cases u
      change Etale (coprod.inl ≫ coprod.desc f g)
      rw [coprod.inl_desc]
      infer_instance
  | inr u =>
      cases u
      change Etale (coprod.inr ≫ coprod.desc f g)
      rw [coprod.inr_desc]
      infer_instance
end
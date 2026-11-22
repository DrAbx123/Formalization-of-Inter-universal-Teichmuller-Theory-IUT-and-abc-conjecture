import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import tmp.sheaf.xif.paper.S1800IdentityAtlasSmallnessActual
import tmp.sheaf.xif.paper.S1839SliceFillingActual
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1831StrongSquareGeometricActual
open LeanFormal.IUT.XiFPaper.S1800IdentityAtlasSmallnessActual
open LeanFormal.IUT.XiFPaper.S1839SliceFillingActual

noncomputable def P : SchemeOverField S1726K :=
  Over.mk (Limits.coprod.desc (Over.Hom.hom (𝟙 S1726AffineOver)) (Over.Hom.hom (𝟙 S1726AffineOver)))

#check P
example : P.left = (S1726AffineOver.left ⨿ S1726AffineOver.left) := rfl
example : IsFinite (Over.Hom.left (𝟙 P)) := by infer_instance
example : IsFinite (Limits.coprod.desc (𝟙 S1726AffineOver.left) (𝟙 S1726AffineOver.left)) := by infer_instance
example : Etale (Limits.coprod.desc (𝟙 S1726AffineOver.left) (𝟙 S1726AffineOver.left)) := by infer_instance
example : IsAffine P.left := by infer_instance
example : Mono (Limits.coprod.inl : S1726AffineOver.left ⟶ P.left) := by infer_instance
example : Limits.coprod.inl ≫ Limits.coprod.desc (𝟙 S1726AffineOver.left) (𝟙 S1726AffineOver.left) = 𝟙 S1726AffineOver.left := by simp
example : Limits.coprod.inr ≫ Limits.coprod.desc (𝟙 S1726AffineOver.left) (𝟙 S1726AffineOver.left) = 𝟙 S1726AffineOver.left := by simp
example : Limits.coprod.desc (𝟙 S1726AffineOver.left) (𝟙 S1726AffineOver.left) ≫ (Over.Hom.hom (𝟙 S1726AffineOver)) =
    Limits.coprod.desc (Over.Hom.hom (𝟙 S1726AffineOver)) (Over.Hom.hom (𝟙 S1726AffineOver)) := by
  rw [Limits.coprod.desc_comp]
  simp

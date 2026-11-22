import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

abbrev X : Scheme.{0} := S1726AffineScheme

example : Etale (Limits.coprod.desc (𝟙 X) (𝟙 X)) := by
  let C := coprodOpenCover.{0, 0} (X := X) (Y := X)
  refine IsZariskiLocalAtSource.of_openCover C ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · change Etale (C.f (Sum.inl PUnit.unit) ≫ Limits.coprod.desc (𝟙 X) (𝟙 X))
    simp only [C, coprodOpenCover, Sum.elim_inl]
    rw [Limits.coprod.inl_desc]
    infer_instance
  · change Etale (C.f (Sum.inr PUnit.unit) ≫ Limits.coprod.desc (𝟙 X) (𝟙 X))
    simp only [C, coprodOpenCover, Sum.elim_inr]
    rw [Limits.coprod.inr_desc]
    infer_instance

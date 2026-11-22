import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

abbrev X : Scheme := S1726AffineScheme

example : IsFinite (Limits.coprod.desc (𝟙 X) (𝟙 X)) := by infer_instance
example : Etale (Limits.coprod.desc (𝟙 X) (𝟙 X)) := by infer_instance
example : IsAffine (X ⨿ X) := by infer_instance
example : Limits.coprod.inl ≫ Limits.coprod.desc (𝟙 X) (𝟙 X) = 𝟙 X := by simp
example : Limits.coprod.inr ≫ Limits.coprod.desc (𝟙 X) (𝟙 X) = 𝟙 X := by simp
#check S1726AffineOver
#check (s1726AffineOver := S1726AffineOver)
example : S1726AffineOver.left = X := rfl
example : (𝟙 S1726AffineOver).left = 𝟙 X := rfl

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Invertibility of actual nonsingular Weierstrass point ideals

The point ideal is invertible as a fractional ideal in the function field.
Transporting its module structure back proves projectivity without a global
Dedekind hypothesis or a false unit-ideal hypothesis on the integral ideal.
The infinity case describes the restriction to the affine chart only.
-/

noncomputable section

namespace LeanFormal.IUT.AffinePunctureIdeal

open scoped nonZeroDivisors
open scoped TensorProduct
open WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)

/-- The integral point ideal and its image in the function field have the same module. -/
def idealFractionalLinearEquiv (I : Ideal W.CoordinateRing) :
    I ≃ₗ[W.CoordinateRing]
      ((I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) :
        Submodule W.CoordinateRing W.FunctionField) :=
  Submodule.equivMapOfInjective (Algebra.linearMap W.CoordinateRing W.FunctionField)
    (IsFractionRing.injective W.CoordinateRing W.FunctionField) I

/-- Nonsingularity supplies the actual inverse fractional ideal already constructed in Mathlib. -/
theorem pointIdeal_invertible {x y : F} (h : W.Nonsingular x y) :
    Module.Invertible W.CoordinateRing
      (CoordinateRing.XYIdeal W x (Polynomial.C y)) := by
  let unitSubmodule : (Submodule W.CoordinateRing W.FunctionField)ˣ :=
    FractionalIdeal.unitsMulEquivSubmodule (S := W.CoordinateRing⁰) (P := W.FunctionField)
      (CoordinateRing.XYIdeal' h)
  letI : Module.Invertible W.CoordinateRing
      (((CoordinateRing.XYIdeal W x (Polynomial.C y) :
          FractionalIdeal W.CoordinateRing⁰ W.FunctionField)) :
        Submodule W.CoordinateRing W.FunctionField) :=
    inferInstanceAs (Module.Invertible W.CoordinateRing unitSubmodule)
  exact Module.Invertible.congr
    (idealFractionalLinearEquiv W (CoordinateRing.XYIdeal W x (Polynomial.C y))).symm

theorem pointIdeal_projective {x y : F} (h : W.Nonsingular x y) :
    Module.Projective W.CoordinateRing
      (CoordinateRing.XYIdeal W x (Polynomial.C y)) := by
  letI := pointIdeal_invertible W h
  infer_instance

theorem pointIdeal_finite {x y : F} (h : W.Nonsingular x y) :
    Module.Finite W.CoordinateRing
      (CoordinateRing.XYIdeal W x (Polynomial.C y)) := by
  letI := pointIdeal_invertible W h
  infer_instance

/-- The actual affine restriction of the point ideal, including the infinity case. -/
def pointVanishingIdeal : W.Point → Ideal W.CoordinateRing
  | .zero => ⊤
  | .some x y _ => CoordinateRing.XYIdeal W x (Polynomial.C y)

theorem pointVanishingIdeal_invertible (P : W.Point) :
    Module.Invertible W.CoordinateRing (pointVanishingIdeal W P) := by
  cases P with
  | zero =>
    exact Module.Invertible.congr (Submodule.topEquiv :
      (⊤ : Submodule W.CoordinateRing W.CoordinateRing) ≃ₗ[W.CoordinateRing]
        W.CoordinateRing).symm
  | some x y h => exact pointIdeal_invertible W h

theorem pointVanishingIdeal_projective (P : W.Point) :
    Module.Projective W.CoordinateRing (pointVanishingIdeal W P) := by
  letI := pointVanishingIdeal_invertible W P
  infer_instance

theorem pointVanishingIdeal_finite (P : W.Point) :
    Module.Finite W.CoordinateRing (pointVanishingIdeal W P) := by
  letI := pointVanishingIdeal_invertible W P
  infer_instance

/-- An invertible module over a domain has rank one without being assumed free. -/
theorem finrank_eq_one_of_invertible
    (R M : Type*) [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Invertible R M] : Module.finrank R M = 1 := by
  have hbase := (TensorProduct.isBaseChange R M (FractionRing R)).finrank_eq
  rw [← hbase]
  exact Module.Invertible.finrank_eq_one (FractionRing R) (FractionRing R ⊗[R] M)

theorem pointIdeal_finrank_eq_one {x y : F} (h : W.Nonsingular x y) :
    Module.finrank W.CoordinateRing
      (CoordinateRing.XYIdeal W x (Polynomial.C y)) = 1 := by
  letI := pointIdeal_invertible W h
  exact finrank_eq_one_of_invertible _ _

theorem pointVanishingIdeal_finrank_eq_one (P : W.Point) :
    Module.finrank W.CoordinateRing (pointVanishingIdeal W P) = 1 := by
  letI := pointVanishingIdeal_invertible W P
  exact finrank_eq_one_of_invertible _ _

end LeanFormal.IUT.AffinePunctureIdeal

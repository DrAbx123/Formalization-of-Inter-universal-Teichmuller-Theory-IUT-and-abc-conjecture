import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineSchemeActual
open Polynomial
open scoped SpecOfNotation
open AlgebraicGeometry

/-- Base ring of the affine Fermat curve: `ℚ[x]`. -/
abbrev FermatBaseRing := Polynomial ℚ

/-- The Fermat equation `y^n + x^n - 1` as a polynomial in `y` over `ℚ[x]`. -/
def fermatPolynomial (n : ℕ) : Polynomial FermatBaseRing :=
  Polynomial.X ^ n + Polynomial.C ((Polynomial.X : Polynomial ℚ) ^ n - 1)

theorem fermatPolynomial_monic {n : ℕ} (hn : n ≠ 0) :
    (fermatPolynomial n).Monic := by
  unfold fermatPolynomial
  exact Polynomial.monic_X_pow_add_C (n := n)
    (a := ((Polynomial.X : Polynomial ℚ) ^ n - 1)) hn

/-- Coordinate ring of the affine Fermat curve `y^n + x^n = 1`. -/
abbrev FermatCurveRing (n : ℕ) := AdjoinRoot (fermatPolynomial n)

/-- The actual scheme-level affine Fermat curve. -/
def fermatCurveScheme (n : ℕ) : Scheme :=
  AlgebraicGeometry.Spec.obj (Opposite.op (CommRingCat.of (FermatCurveRing n)))

/-- The actual finite morphism to the affine base `Spec ℚ[x]`, coming from the
coordinate projection. -/
def fermatToBase (n : ℕ) : fermatCurveScheme n ⟶
    AlgebraicGeometry.Spec.obj (Opposite.op (CommRingCat.of FermatBaseRing)) :=
  Spec.map (CommRingCat.ofHom (algebraMap FermatBaseRing (FermatCurveRing n)))

/-- Finiteness of the coordinate projection: the Fermat curve ring is a finite
module over `ℚ[x]` (the equation is monic in `y`). -/
theorem fermatToBase_module_finite {n : ℕ} (hn : n ≠ 0) :
    Module.Finite FermatBaseRing (FermatCurveRing n) :=
  (fermatPolynomial_monic hn).finite_adjoinRoot

/-- Local derivative of the Fermat equation in the `y` direction. -/
def fermatLocalDerivative (n : ℕ) : Polynomial FermatBaseRing :=
  (fermatPolynomial n).derivative

/-- Actual local derivative formula. -/
theorem fermatLocalDerivative_eq (n : ℕ) :
    fermatLocalDerivative n =
      Polynomial.C (n : FermatBaseRing) * Polynomial.X ^ (n - 1) := by
  unfold fermatLocalDerivative fermatPolynomial
  rw [Polynomial.derivative_add, Polynomial.derivative_C, add_zero]
  exact Polynomial.derivative_X_pow (R := FermatBaseRing) n

#print axioms fermatToBase_module_finite
#print axioms fermatLocalDerivative_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineSchemeActual
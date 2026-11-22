import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoCharts2Actual
open Polynomial
open AlgebraicGeometry
abbrev FermatBase := Polynomial ℚ
def fermatChart0Poly (n : Nat) : Polynomial FermatBase :=
  X ^ n + C (((Polynomial.X : Polynomial ℚ) ^ n) - 1)
theorem fermatChart0Poly_monic (n : Nat) (hn : n ≠ 0) :
    (fermatChart0Poly n).Monic := by
  unfold fermatChart0Poly
  exact Polynomial.monic_X_pow_add_C (n := n)
    (a := ((Polynomial.X : Polynomial ℚ) ^ n - 1)) hn
def fermatChartInfPoly (n : Nat) : Polynomial FermatBase :=
  X ^ n + C (-(1 + (Polynomial.X : Polynomial ℚ) ^ n))
theorem fermatChartInfPoly_monic (n : Nat) (hn : n ≠ 0) :
    (fermatChartInfPoly n).Monic := by
  unfold fermatChartInfPoly
  exact Polynomial.monic_X_pow_add_C (n := n)
    (a := -(1 + (Polynomial.X : Polynomial ℚ) ^ n)) hn
abbrev fermatChart0Ring (n : Nat) : Type := AdjoinRoot (fermatChart0Poly n)
abbrev fermatChartInfRing (n : Nat) : Type := AdjoinRoot (fermatChartInfPoly n)
def fermatChart0 (n : Nat) : Scheme := 
  AlgebraicGeometry.Scheme.Spec.obj (Opposite.op (CommRingCat.of (fermatChart0Ring n)))
def fermatChartInf (n : Nat) : Scheme :=
  AlgebraicGeometry.Scheme.Spec.obj (Opposite.op (CommRingCat.of (fermatChartInfRing n)))
theorem fermatChart0_module_finite (n : Nat) (hn : n ≠ 0) :
    Module.Finite FermatBase (fermatChart0Ring n) :=
  (fermatChart0Poly_monic n hn).finite_adjoinRoot
theorem fermatChartInf_module_finite (n : Nat) (hn : n ≠ 0) :
    Module.Finite FermatBase (fermatChartInfRing n) :=
  (fermatChartInfPoly_monic n hn).finite_adjoinRoot
#print axioms fermatChart0_module_finite
#print axioms fermatChartInf_module_finite
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatTwoCharts2Actual
end
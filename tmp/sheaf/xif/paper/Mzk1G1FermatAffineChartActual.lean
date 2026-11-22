/- G1a Fermat affine chart actual. -/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory
open MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
abbrev A : Type := MvPolynomial (Fin 2) ℚ
def fermatEquation (n : Nat) : A := X 0 ^ n + X 1 ^ n - 1
abbrev R (n : Nat) : Type := A ⧸ Ideal.span {fermatEquation n}
abbrev FermatChart (n : Nat) : Scheme := Spec (CommRingCat.of (R n))
def fermatRelation (n : Nat) : R n := Ideal.Quotient.mk _ (fermatEquation n)
theorem fermatRelation_eq_zero (n : Nat) : fermatRelation n = 0 := by
  rw [fermatRelation, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)
def fermatChartToSpec (n : Nat) : FermatChart n ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (R n)))
#print axioms fermatRelation_eq_zero
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

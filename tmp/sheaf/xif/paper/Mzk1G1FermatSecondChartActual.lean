/- G1a Fermat second affine chart actual. -/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory
open MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
abbrev A : Type := MvPolynomial (Fin 2) ℚ
def secondEquation (n : Nat) : A := 1 + X 0 ^ n - X 1 ^ n
abbrev R2 (n : Nat) : Type := A ⧸ Ideal.span {secondEquation n}
abbrev FermatChart2 (n : Nat) : Scheme := Spec (CommRingCat.of (R2 n))
def secondRelation (n : Nat) : R2 n := Ideal.Quotient.mk _ (secondEquation n)
theorem secondRelation_eq_zero (n : Nat) : secondRelation n = 0 := by
  rw [secondRelation, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)
def fermatChart2ToSpec (n : Nat) : FermatChart2 n ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (R2 n)))
#print axioms secondRelation_eq_zero
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual

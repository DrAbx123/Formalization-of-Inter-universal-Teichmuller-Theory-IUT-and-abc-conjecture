/- G1a Fermat canonical differential actual. -/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic
noncomputable section
open MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCanonicalActual
abbrev A : Type := MvPolynomial (Fin 2) ℚ
def fermatEquation (n : Nat) : A := X 0 ^ n + X 1 ^ n - 1
def fermatDerivativeX (n : Nat) : A := (n : ℚ) • X 0 ^ (n - 1)
def fermatDerivativeY (n : Nat) : A := (n : ℚ) • X 1 ^ (n - 1)
def fermatDifferential (n : Nat) : A := fermatDerivativeX n + fermatDerivativeY n
theorem fermatDifferential_eq (n : Nat) :
    fermatDifferential n = (n : ℚ) • X 0 ^ (n - 1) + (n : ℚ) • X 1 ^ (n - 1) := rfl
theorem fermatEquation_derivative (n : Nat) :
    fermatDifferential n = (n : ℚ) • (X 0 ^ (n - 1) + X 1 ^ (n - 1)) := by
  unfold fermatDifferential fermatDerivativeX fermatDerivativeY
  rw [smul_add]
#print axioms fermatEquation_derivative
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCanonicalActual

/- G1a Fermat ideal sheaf data (standalone actual homogeneous ideal). -/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
noncomputable section
open MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatIdealSheafActual
abbrev A : Type := MvPolynomial (Fin 3) ℚ
def fermatPolynomial (n : ℕ) : A := X 0 ^ n + X 1 ^ n - X 2 ^ n
def fermatIdeal (n : ℕ) : Ideal A := Ideal.span {fermatPolynomial n}
structure FermatIdealSheafData where
  n : ℕ
  I : Ideal A
  eq_fermatIdeal : I = fermatIdeal n
noncomputable def fermatIdealSheafData (n : ℕ) : FermatIdealSheafData where
  n := n
  I := fermatIdeal n
  eq_fermatIdeal := rfl
theorem fermatIdealSheafData_eq (n : ℕ) :
    (fermatIdealSheafData n).I = fermatIdeal n := rfl
#print axioms fermatIdealSheafData_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatIdealSheafActual

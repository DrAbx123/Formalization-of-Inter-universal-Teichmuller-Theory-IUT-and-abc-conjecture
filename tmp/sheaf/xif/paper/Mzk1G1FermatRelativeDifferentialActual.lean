/- G1a Fermat relative differential (standalone actual Kaehler module). -/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic
noncomputable section
open MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatRelativeDifferentialActual
abbrev A : Type := MvPolynomial (Fin 3) ℚ
def fermatPolynomial (n : ℕ) : A := X 0 ^ n + X 1 ^ n - X 2 ^ n
def fermatIdeal (n : ℕ) : Ideal A := Ideal.span {fermatPolynomial n}
abbrev fermatQuotient (n : ℕ) : Type := A ⧸ fermatIdeal n
abbrev fermatRelativeDifferential (n : ℕ) : Type :=
  KaehlerDifferential ℚ (fermatQuotient n)
def fermatDifferentialRank (n : ℕ) : ℕ := n - 3
#check fermatRelativeDifferential
#check fermatDifferentialRank
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatRelativeDifferentialActual

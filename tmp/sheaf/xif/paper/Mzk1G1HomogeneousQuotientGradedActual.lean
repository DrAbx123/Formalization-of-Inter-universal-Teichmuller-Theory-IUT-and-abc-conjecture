/- G1a homogeneous quotient graded algebra attempt. -/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic
noncomputable section
open MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1HomogeneousQuotientGradedActual
abbrev A : Type := MvPolynomial (Fin 3) ℚ
def fermatPolynomial (n : ℕ) : A := X 0 ^ n + X 1 ^ n - X 2 ^ n
def fermatIdeal (n : ℕ) : Ideal A := Ideal.span {fermatPolynomial n}
abbrev homogeneous (i : ℕ) : Submodule ℚ A := MvPolynomial.homogeneousSubmodule (Fin 3) ℚ i
def quotient (n : ℕ) : Type := A ⧸ fermatIdeal n
def quotientComponent (n i : ℕ) : Submodule ℚ (quotient n) :=
  Submodule.map (Ideal.Quotient.mk (fermatIdeal n)).toLinearMap (homogeneous i)
noncomputable def quotientGraded (n : ℕ) :
    GradedAlgebra (quotientComponent n) (quotient n) := by
  infer_instance
#print axioms quotientGraded
end LeanFormal.IUT.XiFPaper.Mzk1G1HomogeneousQuotientGradedActual

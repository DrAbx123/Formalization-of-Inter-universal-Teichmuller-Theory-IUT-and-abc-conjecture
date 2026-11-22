import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.Tactic
set_option relaxedAutoImplicit false
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatQuotientGradedActual
open MvPolynomial AlgebraicGeometry
open scoped Polynomial BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The Fermat polynomial `X0^n + X1^n - X2^n`. -/
noncomputable def fermatPolynomial (n : Nat) : MvPolynomial (Fin 3) ℚ :=
  X 0 ^ n + X 1 ^ n - X 2 ^ n
theorem fermatPolynomial_isHomogeneous (n : Nat) :
    (fermatPolynomial n).IsHomogeneous n := by
  unfold fermatPolynomial
  exact (isHomogeneous_X_pow ..).add (isHomogeneous_X_pow ..) |>.sub (isHomogeneous_X_pow ..)
/-- The Fermat homogeneous ideal. -/
noncomputable def fermatIdeal (n : Nat) : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span {fermatPolynomial n}
/-- The quotient homogeneous coordinate ring. -/
noncomputable abbrev fermatQuotient (n : Nat) : Type :=
  MvPolynomial (Fin 3) ℚ ⧸ fermatIdeal n
/-- Missing frozen-API bundle: a graded algebra structure on the quotient, its
Proj scheme, the closed immersion/subscheme, and smooth/proper/different
properties.  Recorded as a residual structure, not fabricated. -/
structure FermatQuotientGradedRingAPI (n : Nat) where
  grading : Nat → Submodule (fermatQuotient n) (fermatQuotient n)
  gradedRing : Prop
  projScheme : Scheme
  closedImmersion : projScheme ⟶ AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ)
  isClosedImmersion : Prop
  smooth : Prop
  proper : Prop
  different : Prop
def fermatQuotientGradedRingMissing (n : Nat) : Prop :=
  Nonempty (FermatQuotientGradedRingAPI n)
#print axioms fermatPolynomial_isHomogeneous
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatQuotientGradedActual
end
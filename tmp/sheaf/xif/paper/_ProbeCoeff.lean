import Mathlib.Algebra.MvPolynomial.Degrees
noncomputable section
open MvPolynomial
variable (K : Type) [Field K]
example : MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 3)
    (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0 : MvPolynomial (Fin 2) K) = -1 := by
  simp [MvPolynomial.coeff_add, MvPolynomial.coeff_sub, MvPolynomial.coeff_X_pow, Finsupp.single_eq_same]

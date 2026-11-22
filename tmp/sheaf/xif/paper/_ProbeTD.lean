import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic.ComputeDegree
noncomputable section
open MvPolynomial
variable (K : Type) [Field K] [DecidableEq K]
example : (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0 : MvPolynomial (Fin 2) K).totalDegree = 3 := by
  native_decide

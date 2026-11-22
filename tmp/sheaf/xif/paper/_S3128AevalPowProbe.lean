import Mathlib.Algebra.Polynomial.Eval.Defs
open Polynomial
variable {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (x : A) (n : ℕ)
#check Polynomial.aeval_X_pow
#check Polynomial.aeval_pow
#check Polynomial.aeval_monomial
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

universe u
namespace S1923Net
open scoped nonZeroDivisors

lemma X_mem_nonZeroDivisors_poly (R : Type u) [CommRing R] :
    (Polynomial.X : Polynomial R) ∈ nonZeroDivisors (Polynomial R) := by
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro a ha
    ext n
    have h := congrArg (fun p : Polynomial R => p.coeff (n + 1)) ha
    simpa [Polynomial.coeff_X_mul] using h
  · intro a ha
    ext n
    have h := congrArg (fun p : Polynomial R => p.coeff (n + 1)) ha
    simpa [Polynomial.coeff_mul_X] using h

end S1923Net

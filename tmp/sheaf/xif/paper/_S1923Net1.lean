import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Polynomial.Basic

universe u

namespace S1923Net

open IsEllipticNet

variable {R : Type u} [CommRing R] (W : ℤ → R)

lemma atomRel_even (m : ℤ) : atomRel W (2 * m + 2) (2 * m - 2) 2 0 =
    W (2 * m) * W 2 * W 1 ^ 2 - W (m - 1) ^ 2 * W m * W (m + 2) +
      W (m - 2) * W m * W (m + 1) ^ 2 := by
  have h : atomRel W (2 * m + 2) (2 * m - 2) 2 0 = rel W (m + 1) (m - 1) 1 0 := by
    rw [rel_eq]
    ring_nf
  rw [h, rel_even]

lemma atomRel_odd (m : ℤ) : atomRel W (2 * m + 2) (2 * m) 2 0 =
    W (2 * m + 1) * W 1 ^ 3 - W (m + 2) * W m ^ 3 + W (m - 1) * W (m + 1) ^ 3 := by
  have h : atomRel W (2 * m + 2) (2 * m) 2 0 = rel W (m + 1) m 1 0 := by
    rw [rel_eq]
    ring_nf
  rw [h, rel_odd]

end S1923Net

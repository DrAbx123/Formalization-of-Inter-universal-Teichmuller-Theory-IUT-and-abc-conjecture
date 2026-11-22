import Mathlib.NumberTheory.EllipticDivisibilitySequence
universe u
namespace S1923Net
open IsEllipticNet
variable {R : Type u} [CommRing R] (W : ℤ → R)
lemma foo (a b c d e f : ℤ) {u v w x y z : R} (h : u + v + w + x + y + z = 0) :
    (u + v) * atom W a b * atomRel W c d e f = 0 := by
  simp only [atomRel]
  grind only
end S1923Net

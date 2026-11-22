import tmp.sheaf.xif.paper.S1923NetD1
import tmp.sheaf.xif.paper.S1923NetC

universe u
namespace S1923Net
open IsEllipticNet
open scoped nonZeroDivisors

variable {R : Type u} [CommRing R] (W : ℤ → R)

protected lemma IsEllipticNet.comp {W : ℤ → R} {S : Type*} [CommRing S] (h : IsEllipticNet W)
    (f : R →+* S) : IsEllipticNet (f ∘ W) := fun p q r s => by
  rw [← IsEllipticNet.map_rel, h, map_zero]

theorem IsEllipticNet.of_even_odd (neg : W.Odd) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (even : ∀ m : ℤ, rel W (m + 1) (m - 1) 1 0 = 0)
    (odd : ∀ m : ℤ, rel W (m + 1) m 1 0 = 0) : IsEllipticNet W := by
  intro p q r s
  rw [rel_eq]
  apply atomRel_of_even_odd neg one two
  · intro m
    have h := even m
    rw [rel_eq] at h
    simpa [show 2 * (m + 1) + 0 = 2 * m + 2 by ring,
      show 2 * (m - 1) + 0 = 2 * m - 2 by ring, show 2 * 1 + 0 = 2 by norm_num] using h
  · intro m
    have h := odd m
    rw [rel_eq] at h
    simpa [show 2 * (m + 1) + 0 = 2 * m + 2 by ring,
      show 2 * m + 0 = 2 * m by ring, show 2 * 1 + 0 = 2 by norm_num] using h
  · grind

end S1923Net

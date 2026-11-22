import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Polynomial.Basic

universe u

namespace S1923Net

open IsEllipticNet

variable {R : Type u} [CommRing R] (W : ℤ → R)

noncomputable def sortDesc {n : ℕ} {α : Type*} [LinearOrder α] (f : Fin n → α) : Equiv.Perm (Fin n) :=
  Fin.revPerm.trans (Tuple.sort f)

lemma antitone_sortDesc {n : ℕ} {α : Type*} [LinearOrder α] (f : Fin n → α) :
    Antitone (f ∘ sortDesc f) := by
  intro i j hij
  exact (Tuple.monotone_sort f) (Fin.rev_le_rev.mpr hij)

variable {W} in
lemma neg_atomRel₁₂ (neg : W.Odd) (a b c d : ℤ) : -atomRel W a b c d = atomRel W b a c d := by
  grind only [atomRel, neg_atom]

variable {W} in
lemma neg_atomRel₂₃ (neg : W.Odd) (a b c d : ℤ) : -atomRel W a b c d = atomRel W a c b d := by
  grind only [atomRel, neg_atom]

variable {W} in
lemma neg_atomRel₃₄ (neg : W.Odd) (a b c d : ℤ) : -atomRel W a b c d = atomRel W a b d c := by
  grind only [atomRel, neg_atom]

variable {W} in
lemma atomRel_neg (neg : W.Odd) (a b c d : ℤ) :
    atomRel W (-a) (-b) (-c) (-d) = atomRel W a b c d := by
  rw [atomRel_neg₁ neg, atomRel_neg₂ neg, atomRel_neg₃ neg, atomRel_neg₄]

variable {W} in
lemma atomRel_abs (neg : W.Odd) (a b c d : ℤ) :
    atomRel W |a| |b| |c| |d| = atomRel W a b c d := by
  rw [atomRel_abs₁ neg, atomRel_abs₂ neg, atomRel_abs₃ neg, atomRel_abs₄]

lemma atomRel_avg_sub_pairwise {a b c d : ℤ} (parity : [a, b, c, d].Pairwise (· % 2 = · % 2)) :
    atomRel W ((a + b + c + d) / 2 - d) ((a + b + c + d) / 2 - c) ((a + b + c + d) / 2 - b)
      ((a + b + c + d) / 2 - a) = atomRel W a b c d := by
  simp_rw [add_assoc <| a + b, atomRel, atom, sub_add_sub_comm, ← two_mul]
  repeat rw [Int.mul_ediv_cancel'] <;> grind

lemma atomRel_even (m : ℤ) : atomRel W (2 * m + 2) (2 * m - 2) 2 0 =
    W (2 * m) * W 2 * W 1 ^ 2 - W (m - 1) ^ 2 * W m * W (m + 2) +
      W (m - 2) * W m * W (m + 1) ^ 2 := by
  have h : atomRel W (2 * m + 2) (2 * m - 2) 2 0 = rel W (m + 1) (m - 1) 1 0 := by
    rw [rel_eq]; ring_nf
  rw [h, rel_even]

lemma atomRel_odd (m : ℤ) : atomRel W (2 * m + 2) (2 * m) 2 0 =
    W (2 * m + 1) * W 1 ^ 3 - W (m + 2) * W m ^ 3 + W (m - 1) * W (m + 1) ^ 3 := by
  have h : atomRel W (2 * m + 2) (2 * m) 2 0 = rel W (m + 1) m 1 0 := by
    rw [rel_eq]; ring_nf
  rw [h, rel_odd]

end S1923Net

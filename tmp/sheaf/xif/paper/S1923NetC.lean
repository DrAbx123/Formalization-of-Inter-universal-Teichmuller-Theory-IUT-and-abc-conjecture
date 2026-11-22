import tmp.sheaf.xif.paper.S1923NetB
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation

universe u
namespace S1923Net
open IsEllipticNet
open scoped nonZeroDivisors
variable {R : Type u} [CommRing R] (W : ℤ → R)

variable {W} in
lemma atomRel_of_even_odd (neg : W.Odd) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (even : ∀ m : ℤ, atomRel W (2 * m + 2) (2 * m - 2) 2 0 = 0)
    (odd : ∀ m : ℤ, atomRel W (2 * m + 2) (2 * m) 2 0 = 0) {a b c d : ℤ}
    (parity : [a, b, c, d].Pairwise (· % 2 = · % 2)) : atomRel W a b c d = 0 := by
  wlog _ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d generalizing a b c d with h
  · exact atomRel_abs neg .. ▸ h (parity.map _ <| by grind) <| by simp
  wlog _ : d ≤ c ∧ c ≤ b ∧ b ≤ a generalizing a b c d with h
  · rw [← atomRel_perm neg (sortDesc ![a, b, c, d]) a b c d, smul_eq_zero_iff_eq]
    refine h (parity.perm (Equiv.Perm.ofFn_comp_perm _ ![a, b, c, d]).symm .symm) ?_ ?_
    · split_ands <;> apply (fun i ↦ by fin_cases i <;> simp <;> omega : 0 ≤ ![a, b, c, d])
    · split_ands <;> exact antitone_sortDesc _ <| by decide
  wlog _ : d < c ∧ c < b ∧ b < a
  · rcases (by omega : a = b ∨ b = c ∨ c = d) with rfl | rfl | rfl <;>
      simp [pow_mem two 3 |>.right (W 0) <| by grind only [atomRel_same₂₃, atom, odd 1]]
  replace parity : a % 2 = b % 2 ∧ b % 2 = c % 2 ∧ c % 2 = d % 2 := by grind
  induction hn : 4 * a + b + c + d using @Int.strongRec 0 generalizing a b c d with
  | lt => omega
  | ge _ _ ih =>
    replace ih (a b c d : ℤ) := (@ih (4 * a + b + c + d) · a b c d)
    wlog _ : c = a % 2 + 2
    · have ha : atom W (a % 2 + 2) (a % 2) ∈ R⁰ := by grind only [atom, mul_mem]
      exact ha.left _ <| by grind (genLocal := 0) [atom_same, atomRel_same₃₄,
        atomRel.eq_def W a b c, @atom_mul_atomRel R _ W a b c (max d <| a % 2 + 2)
          (min d <| a % 2 + 2) (a % 2) 0 0 0 (-1) 0 1 <| by norm_num1, = (ih)]
    wlog _ : a = b + 2
    · grind (genLocal := 0) [=_ atomRel_neg₄, @atomRel_avg_sub_pairwise R _ W a b c d <| by grind, = (ih)]
    grind [odd (b / 2), atomRel_neg₄ W a b c d, atomRel_avg_sub_pairwise W (by simp) |>.trans (even (a / 2))]

end S1923Net

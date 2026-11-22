import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Group.Action.Units
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# S1491: the canonical normalised EDS is an elliptic net

This file ports the short proof of `IsEllipticNet.normEDS` that Mathlib master carries on top of
v4.32.2 (commit `d268775514`, "prove that a normalised elliptic divisibility sequence is an
elliptic sequence").  The only public additions are `IsEllipticNet.of_even_odd`,
`IsEllipticNet.normEDS` and `IsEllipticSequence.normEDS`; the auxiliary relator identities are
kept close to the source proof.

The proof strategy is:
* `atomRel_of_even_odd`: the four-index atom relator vanishes for all same-parity quadruples once
  the even and odd doubling relators vanish and `W 1`, `W 2` are nonzerodivisors;
* `IsEllipticNet.of_even_odd`: translate this back through `rel_eq`;
* `IsEllipticNet.normEDS`: specialise the universal `normEDS` over `R[X]` along `eval b`.
-/

noncomputable section

open scoped nonZeroDivisors
open Polynomial

universe u v

namespace S1491

/-- Descending sort of a tuple, the antitone counterpart of `Tuple.sort`.  This is
`Tuple.sortDesc` from Mathlib master, which is not yet in v4.32.2. -/
def sortDesc {n : ℕ} {α : Type*} [LinearOrder α] (f : Fin n → α) : Equiv.Perm (Fin n) :=
  Tuple.sort (OrderDual.toDual ∘ f)

/-- The descending sort is antitone. -/
theorem antitone_sortDesc {n : ℕ} {α : Type*} [LinearOrder α] (f : Fin n → α) :
    Antitone (f ∘ sortDesc f) := by
  have hmono : Monotone ((OrderDual.toDual ∘ f) ∘ Tuple.sort (OrderDual.toDual ∘ f)) :=
    Tuple.monotone_sort _
  rw [Function.comp_assoc] at hmono
  exact monotone_toDual_comp_iff.mp hmono

end S1491

namespace IsEllipticNet

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {W : ℤ → R}
variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

/-- Pairwise-parity version of `atomRel_avg_sub`. -/
lemma atomRel_avg_sub_pairwise {a b c d : ℤ}
    (parity : [a, b, c, d].Pairwise (· % 2 = · % 2)) :
    atomRel W ((a + b + c + d) / 2 - d) ((a + b + c + d) / 2 - c) ((a + b + c + d) / 2 - b)
      ((a + b + c + d) / 2 - a) = atomRel W a b c d := by
  apply atomRel_avg_sub
  grind

lemma neg_atomRel₁₂ (neg : W.Odd) (a b c d : ℤ) : -atomRel W a b c d = atomRel W b a c d := by
  grind only [atomRel, neg_atom]

lemma neg_atomRel₂₃ (neg : W.Odd) (a b c d : ℤ) : -atomRel W a b c d = atomRel W a c b d := by
  grind only [atomRel, neg_atom]

lemma neg_atomRel₃₄ (neg : W.Odd) (a b c d : ℤ) : -atomRel W a b c d = atomRel W a b d c := by
  grind only [atomRel, neg_atom]

lemma atomRel_neg (neg : W.Odd) (a b c d : ℤ) :
    atomRel W (-a) (-b) (-c) (-d) = atomRel W a b c d := by
  rw [atomRel_neg₁ neg, atomRel_neg₂ neg, atomRel_neg₃ neg, atomRel_neg₄]

lemma atomRel_abs (neg : W.Odd) (a b c d : ℤ) :
    atomRel W |a| |b| |c| |d| = atomRel W a b c d := by
  rw [atomRel_abs₁ neg, atomRel_abs₂ neg, atomRel_abs₃ neg, atomRel_abs₄]

/-- The even atom relator `ERₐ(2 * m + 2, 2 * m - 2, 2, 0)`. -/
lemma atomRel_even (m : ℤ) : atomRel W (2 * m + 2) (2 * m - 2) 2 0 = W (2 * m) * W 2 * W 1 ^ 2 -
    W (m - 1) ^ 2 * W m * W (m + 2) + W (m - 2) * W m * W (m + 1) ^ 2 := by
  grind only [atomRel, atom]

/-- The odd atom relator `ERₐ(2 * m + 2, 2 * m, 2, 0)`. -/
lemma atomRel_odd (m : ℤ) : atomRel W (2 * m + 2) (2 * m) 2 0 =
    W (2 * m + 1) * W 1 ^ 3 - W (m + 2) * W m ^ 3 + W (m - 1) * W (m + 1) ^ 3 := by
  grind only [atomRel, atom]

/-- The fundamental six-index atom identity behind the descent. -/
lemma atom_mul_atomRel (a b c d e f : ℤ) {u v w x y z : R} (h : u + v + w + x + y + z = 0) :
    (u + v) * atom W a b * atomRel W c d e f - (u + w) * atom W a c * atomRel W b d e f +
    (u + x) * atom W a d * atomRel W b c e f - (u + y) * atom W a e * atomRel W b c d f +
    (u + z) * atom W a f * atomRel W b c d e + (v + w) * atom W b c * atomRel W a d e f -
    (v + x) * atom W b d * atomRel W a c e f + (v + y) * atom W b e * atomRel W a c d f -
    (v + z) * atom W b f * atomRel W a c d e + (w + x) * atom W c d * atomRel W a b e f -
    (w + y) * atom W c e * atomRel W a b d f + (w + z) * atom W c f * atomRel W a b d e +
    (x + y) * atom W d e * atomRel W a b c f - (x + z) * atom W d f * atomRel W a b c e +
    (y + z) * atom W e f * atomRel W a b c d = 0 := by
  simp only [atomRel]
  grind only

/-- `atomRel` is invariant under permutations of the four indices, up to the sign. -/
lemma atomRel_perm (neg : W.Odd) (σ : Equiv.Perm <| Fin 4) (a b c d : ℤ) :
    σ.sign • atomRel W (![a, b, c, d] <| σ 0) (![a, b, c, d] <| σ 1) (![a, b, c, d] <| σ 2)
      (![a, b, c, d] <| σ 3) = atomRel W a b c d := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap σ x y _ _ => fin_cases x <;> fin_cases y <;> simp [Equiv.swap_apply_def] <;>
      grind only [neg_atomRel₁₂, neg_atomRel₂₃, neg_atomRel₃₄, smul_neg]

/-- **The descending induction for the four-index atom relator.**  If the even and odd doubling
relations hold and `W 1`, `W 2` are nonzerodivisors, then every same-parity four-index atom
relator vanishes. -/
lemma atomRel_of_even_odd (neg : W.Odd) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (even : ∀ m : ℤ, atomRel W (2 * m + 2) (2 * m - 2) 2 0 = 0)
    (odd : ∀ m : ℤ, atomRel W (2 * m + 2) (2 * m) 2 0 = 0) {a b c d : ℤ}
    (parity : [a, b, c, d].Pairwise (· % 2 = · % 2)) : atomRel W a b c d = 0 := by
  have hW0 : W 0 = 0 := by
    have h := even 0
    rw [atomRel_even] at h
    norm_num at h
    rw [neg 1, neg 2] at h
    have h2 : W 0 * W 2 * W 1 ^ 2 = 0 := by linear_combination -h
    have h3 : W 0 * W 2 = 0 :=
      (IsRegular.right (isRegular_iff_mem_nonZeroDivisors.mpr (pow_mem one 2)))
        (by simpa [mul_assoc] using h2)
    exact (IsRegular.right (isRegular_iff_mem_nonZeroDivisors.mpr two)) (by simpa using h3)
  wlog _ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d generalizing a b c d with h
  · exact atomRel_abs neg .. ▸ h (parity.map _ <| by grind) <| by simp
  wlog _ : d ≤ c ∧ c ≤ b ∧ b ≤ a generalizing a b c d with h
  · rw [← atomRel_perm neg (S1491.sortDesc ![a, b, c, d]) a b c d, smul_eq_zero_iff_eq]
    refine h (parity.perm (Equiv.Perm.ofFn_comp_perm _ ![a, b, c, d]).symm .symm) ?_ ?_
    · split_ands <;> apply (fun i ↦ by fin_cases i <;> simp <;> omega : 0 ≤ ![a, b, c, d])
    · split_ands <;> exact S1491.antitone_sortDesc _ <| by decide
  wlog _ : d < c ∧ c < b ∧ b < a
  · rcases (by omega : a = b ∨ b = c ∨ c = d) with rfl | rfl | rfl <;>
      simp [hW0]
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
    · grind (genLocal := 0) [=_ atomRel_neg₄, @atomRel_avg_sub_pairwise R _ W a b c d <| by grind,
        = (ih)]
    grind [odd (b / 2), atomRel_neg₄ W a b c d,
      atomRel_avg_sub_pairwise (W := W) (by simp) |>.trans (even (a / 2))]

/-- The composition of an elliptic net with a ring hom is an elliptic net. -/
protected lemma comp (h : IsEllipticNet W) (f : F) : IsEllipticNet <| f ∘ W :=
  fun _ _ _ _ ↦ by rw [← map_rel (f := f), h, map_zero]

/-- If a sequence satisfies the even and odd elliptic relations, then it is an elliptic net. -/
theorem of_even_odd (neg : W.Odd) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (even : ∀ m : ℤ, rel W (m + 1) (m - 1) 1 0 = 0) (odd : ∀ m : ℤ, rel W (m + 1) m 1 0 = 0) :
    IsEllipticNet W := fun _ _ _ _ ↦ by
  simp_rw [rel_eq] at *
  apply atomRel_of_even_odd <;> grind

end IsEllipticNet

section NormEDS

variable {R : Type u} [CommRing R] (b c d : R)

lemma normEDS_atomRel_even (m : ℤ) :
    IsEllipticNet.atomRel (normEDS b c d) (2 * m + 2) (2 * m - 2) 2 0 = 0 := by
  simp [IsEllipticNet.atomRel_even, normEDS_even]

lemma normEDS_atomRel_odd (m : ℤ) :
    IsEllipticNet.atomRel (normEDS b c d) (2 * m + 2) (2 * m) 2 0 = 0 := by
  simp [IsEllipticNet.atomRel_odd, normEDS_odd]

lemma normEDS_rel_even (m : ℤ) : IsEllipticNet.rel (normEDS b c d) (m + 1) (m - 1) 1 0 = 0 := by
  simp [IsEllipticNet.rel_even, normEDS_even]

lemma normEDS_rel_odd (m : ℤ) : IsEllipticNet.rel (normEDS b c d) (m + 1) m 1 0 = 0 := by
  simp [IsEllipticNet.rel_odd, normEDS_odd]

open Polynomial in
/-- The canonical normalised EDS is an elliptic net. -/
theorem IsEllipticNet.normEDS : IsEllipticNet <| normEDS b c d := by
  suffices h : IsEllipticNet <| _root_.normEDS (X : R[X]) (C c) (C d) by
    convert h.comp <| evalRingHom b
    simp_rw [Function.comp_def, map_normEDS, coe_evalRingHom, eval_X, eval_C]
  exact of_even_odd (normEDS_neg X _ _) (by simp)
    (by simpa using Polynomial.isRegular_X.mem_nonZeroDivisors)
    (normEDS_rel_even _ _ _) (normEDS_rel_odd _ _ _)

/-- The canonical normalised EDS is an elliptic sequence. -/
theorem IsEllipticSequence.normEDS : IsEllipticSequence <| normEDS b c d :=
  IsEllipticNet.normEDS b c d |>.isEllipticSequence

end NormEDS

section RelThree

variable {R : Type u} [CommRing R] (b c d : R)

/-- The three-index elliptic relation (Rel₃) for `normEDS`. -/
theorem rel3_normEDS (m n r : ℤ) :
    normEDS b c d (m + n) * normEDS b c d (m - n) * normEDS b c d r ^ 2 =
      normEDS b c d (m + r) * normEDS b c d (m - r) * normEDS b c d n ^ 2 -
        normEDS b c d (n + r) * normEDS b c d (n - r) * normEDS b c d m ^ 2 := by
  have h := IsEllipticSequence.normEDS b c d m n r
  simp only [IsEllipticNet.rel, add_zero] at h
  linear_combination h

/-- The special relation `Rel₃(n, 2, n - 1)` used by S1377. -/
theorem rel3_special_normEDS (n : ℤ) :
    normEDS b c d (n + 2) * normEDS b c d (n - 2) * normEDS b c d (n - 1) ^ 2 =
      normEDS b c d (2 * n - 1) * b ^ 2 -
        normEDS b c d (n + 1) * normEDS b c d (3 - n) * normEDS b c d n ^ 2 := by
  have h := rel3_normEDS b c d n 2 (n - 1)
  simpa only [normEDS_one, normEDS_two,
    show n + (n - 1) = 2 * n - 1 by ring,
    show n - (n - 1) = 1 by ring,
    show 2 + (n - 1) = n + 1 by ring,
    show 2 - (n - 1) = 3 - n by ring,
    mul_one, one_pow] using h

end RelThree

section DivisionPolynomial

open WeierstrassCurve

/-- The bivariate division-polynomial sequence `ψ` is an elliptic net.  This is the missing
input `isEllipticNet_ψ` of the TauCeti `ZSMul` bridge. -/
theorem isEllipticNet_ψ {F : Type u} [Field F] (W : WeierstrassCurve F) :
    IsEllipticNet W.ψ := by
  have h : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl
  rw [h]
  exact IsEllipticNet.normEDS _ _ _

/-- The point-level evaluation `n ↦ ψₙ(x, y)` of the bivariate division polynomials is an
elliptic net. -/
theorem isEllipticNet_evalEval_ψ {F : Type u} [Field F] (W : WeierstrassCurve F) (x y : F) :
    IsEllipticNet (fun n : ℤ => Polynomial.evalEval x y (W.ψ n)) := by
  have h := (isEllipticNet_ψ W).comp (Polynomial.evalEvalRingHom x y)
  simpa only [Function.comp_def, Polynomial.coe_evalEvalRingHom] using h

end DivisionPolynomial

/-- The exact target, checked at the expected type. -/
example {R : Type u} [CommRing R] (b c d : R) : IsEllipticNet (normEDS b c d) :=
  IsEllipticNet.normEDS b c d

#check @IsEllipticNet.normEDS
#print axioms IsEllipticNet.of_even_odd
#print axioms IsEllipticNet.normEDS
#print axioms IsEllipticSequence.normEDS
#print axioms normEDS_rel_even
#print axioms normEDS_rel_odd
#print axioms rel3_normEDS
#print axioms rel3_special_normEDS
#print axioms isEllipticNet_ψ
#print axioms isEllipticNet_evalEval_ψ

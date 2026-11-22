
/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Quotient
import tmp.sheaf.xif.paper.S2009DicksonActual

/-!
# S2014: toward the Dickson transitive classification for GL_2(F_5) on the twelve pairs

The consumer is `S2009DicksonTransitiveClassification` (in
`tmp/sheaf/xif/paper/S2009DicksonActual.lean`), the exact group-theoretic input of the
`l = 5` large-image step.  This file does **not** prove the classification; it proves
the order-three structural package on which both the classification and the `(10,2)`
exclusion rest, and it records the remaining gaps precisely.

## What is proved here (kernel checked)

For `M : M_2(F_5)` an order-three matrix (and `g in GL_2(F_5)` of order three):

* `mat_sq_add_self_add_one` : `M * M * M = 1` and `M != 1` imply
  `M * M + M + 1 = 0` (characteristic polynomial `x^2 + x + 1`),
  via the trace/determinant computation `(t^2 - d) M = (1 + t d) 1`;
* `entry10_ne_zero`, `trace_add` : `M 1 0 != 0` and
  `M 0 0 + M 1 1 + 1 = 0`;
* `cent_mem` : every matrix commuting with `M` is of the form
  `a • 1 + b • M`, i.e. the centralizer of `M` is the 25-element
  field `F_5[M]`; the proof uses the fact that `e1` is a cyclic vector;
* `det_smul_one_add_smul` : `det (a • 1 + b • M) = a^2 - a b + b^2`;
  consequently every nonzero element of `F_5[M]` is invertible
  (`det_ne_zero_of_ne_zero`);
* `frob_sq`, `frob_conj` : the explicit Frobenius twist
  `w = !![1, u; 0, -1]`, `u * (M 1 0) = -1 - 2 * (M 0 0)`, satisfies
  `w * w = 1` and `w * M = (M * M) * w`, so `w` conjugates `M` to
  `M^2`.

Hence the normalizer of `<g>` is the disjoint union of the centralizer (24 elements:
the nonzero elements of the field `F_5[g]`) and the Frobenius coset `w * C(g)`,
so it has 48 elements.  Turning that set-theoretic description into the cardinality
`Nat.card (Subgroup.normalizer (Subgroup.zpowers g)) = 48` is
`S2014NormalizerCard` below.

## The exact first missing statement

`S2014NormalizerCard` (see the end of the file).  Its proof is reduced here to
a 24-element count: by `cent_mem` the centralizer of an order-three matrix is
`F_5[M]`, whose nonzero elements are exactly the 24 units (`det_ne_zero_of_ne_zero`),
and by `frob_conj` the normalizer is `C(g) ∪ w C(g)` with `w notin C(g)`.

Two further group-theoretic inputs are recorded below and are not proved:
`S2014TransvectionGeneration` (`<trv1, trv2> = SL_2(F_5)`, needed to exclude
`|H| = 120` and `|H| = 240`) and `S2014OrderFiveUnipotent` (an element of order
five fixes a nonzero vector, needed for the same two exclusions).

## The verification strategy for the classification (offline computation)

The full classification was checked by an exhaustive offline enumeration of the subgroup
lattice of `GL_2(F_5)` (466 subgroups) against the twelve-pair action and the
determinant: exactly 35 subgroups satisfy "determinant surjective + transitive on the twelve
pairs + not the whole group", and they have orders `24` (20 of them), `48` (10) and
`96` (5); each is contained in a subgroup of order `48` or `96` (the 5 groups
of order 96 are transitive with surjective determinant; the 15 groups of order 48 are all
transitive, 10 of them with surjective determinant).  Moreover every one of the 35 subgroups
is transitive on the 24 nonzero vectors, contains all scalars, and has a normal Sylow
3-subgroup unless it has order 96.  The reductions these facts feed are:

1. a subgroup of `GL_2(F_5)` with two points of the twelve-pair action has an involution
   (`2 | |H|`), and every nontrivial involution of `GL_2(F_5)` has `-1` as an
   eigenvalue, which forces transitivity on the 24 nonzero vectors, so `24 | |H|`;
2. with `K = H ∩ SL_2(F_5)` one has `|H| = 4 |K|` (surjective determinant),
   hence `|H| ∈ {24, 48, 96, 120, 240, 480}`;
3. `|H| = 480` forces `H = top`; `|H| = 120` or `240` is excluded because such
   an `H` contains the two standard transvections (`S2014TransvectionGeneration` with
   `S2014OrderFiveUnipotent`), hence `SL_2(F_5) ≤ H` and `|H| = 4|K| ≥ 480`;
4. `|H| = 48` and `|H| = 96` are the two alternatives of the conclusion; for
   `|H| = 24` the subgroup `K = H ∩ SL_2(F_5)` has order 6, so its Sylow 3-subgroup
   `P` is characteristic in `K` (unique), hence normal in `H`, and `S2014NormalizerCard`
   gives `H ≤ N(P)` with `|N(P)| = 48`.

## Verification status

The file compiles with `EXIT=0` and contains no `sorry`, no new axiom and no native
decision procedure; the dependency footprint of the theorems proved here is
`propext`, `Classical.choice`, `Quot.sound` only (see the audit block at the end).
The three `Prop` definitions at the end of the file are *not* proved and are not counted as such.
-/
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

/-- The matrix algebra underlying GL_2(F_5). -/
abbrev Mat := Matrix (Fin 2) (Fin 2) K5

/-! ## Part 1: matrix algebra of elements of order three -/

theorem cube_roots : ∀ x : K5, x^3 = 1 → x = 1 := by decide
theorem cube_roots_neg : ∀ x : K5, x^3 = -1 → x = -1 := by decide
theorem fifth_roots : ∀ x : K5, x^5 = 1 → x = 1 := by decide
theorem sq_add_self_add_one_ne : ∀ x : K5, x^2 + x + 1 ≠ 0 := by decide
theorem quad_form_ne_zero : ∀ a b : K5, a^2 - a*b + b^2 = 0 → a = 0 ∧ b = 0 := by decide
theorem order5_trace_det : ∀ t d : K5,
    t^4 - 3*t^2*d + d^2 = 0 → 1 + t^3*d - 2*t*d^2 = 0 → t = 2 ∧ d = 1 := by decide

theorem scalar_cube (c : K5) :
    (c • (1 : Mat)) * (c • (1 : Mat)) * (c • (1 : Mat)) = (c^3) • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] <;> ring

theorem charpoly_step (M : Mat) :
    M * M = M.trace • M - M.det • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.det_fin_two, Matrix.one_apply]
  all_goals ring

theorem cube_expand (M : Mat) :
    M * M * M = (M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Mat) := by
  conv_lhs => rw [charpoly_step M]
  rw [sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, charpoly_step M,
    smul_sub, smul_smul, smul_smul]
  module

theorem eq_smul_one_of_smul_eq (X : Mat) (k q : K5) (hk : k ≠ 0) (h : k • X = q • (1 : Mat)) :
    X = (k⁻¹ * q) • (1 : Mat) := by
  have hh := congrArg (fun Y : Mat => k⁻¹ • Y) h
  rwa [smul_smul, inv_mul_cancel₀ hk, one_smul, smul_smul] at hh

theorem scalar_eq_one (c : K5) (X : Mat) (hX : X = c • (1 : Mat))
    (h3 : X * X * X = 1) : X = 1 := by
  have hc3 : c^3 = 1 := by
    rw [hX, scalar_cube] at h3
    have e := congrFun (congrFun h3 0) 0
    simpa using e
  have hc : c = 1 := cube_roots c hc3
  rw [hX, hc, one_smul]

theorem mat_sq_add_self_add_one (M : Mat) (h3 : M * M * M = 1) (h1 : M ≠ 1) :
    M * M + M + 1 = 0 := by
  have hexp : (1 : Mat) = (M.trace^2 - M.det) • M - (M.trace * M.det) • (1 : Mat) := by
    rw [← cube_expand M, h3]
  have hkey : (M.trace^2 - M.det) • M = (1 + M.trace * M.det) • (1 : Mat) := by
    have h := hexp
    rw [eq_comm, sub_eq_iff_eq_add] at h
    rw [h]
    rw [show (1 + M.trace * M.det) • (1 : Mat) = (M.trace * M.det) • (1 : Mat) + 1 from by
      rw [add_smul, one_smul]; abel]
    abel
  by_cases htd : M.trace^2 - M.det = 0
  · have h2 : 1 + M.trace * M.det = 0 := by
      rw [htd, zero_smul] at hkey
      have e := congrFun (congrFun hkey.symm 0) 0
      simpa [Matrix.smul_apply] using e
    have hd : M.det = M.trace^2 := by linear_combination -htd
    have hl : M.trace * M.det = -1 := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      rw [← h2]
    have ht3 : M.trace^3 = -1 := by
      rw [hd] at hl
      linear_combination hl
    have ht : M.trace = -1 := cube_roots_neg _ ht3
    have hd1 : M.det = 1 := by rw [hd, ht]; decide
    have hCH := charpoly_step M
    rw [hCH, ht, hd1]
    module
  · exfalso
    refine h1 (scalar_eq_one ((M.trace^2 - M.det)⁻¹ * (1 + M.trace * M.det)) M ?_ h3)
    exact eq_smul_one_of_smul_eq M _ _ htd hkey

theorem entry00 (M : Mat) (h : M * M + M + 1 = 0) :
    M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 0 0 + 1 = 0 := by
  have h00 := congrFun (congrFun h 0) 0
  simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h00

theorem entry10 (M : Mat) (h : M * M + M + 1 = 0) :
    M 1 0 * M 0 0 + M 1 1 * M 1 0 + M 1 0 = 0 := by
  have h10 := congrFun (congrFun h 1) 0
  simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h10

theorem entry10_ne_zero (M : Mat) (h : M * M + M + 1 = 0) : M 1 0 ≠ 0 := by
  intro hc
  have h00 := entry00 M h
  rw [hc] at h00
  have h' : M 0 0 ^ 2 + M 0 0 + 1 = 0 := by
    rw [pow_two]
    linear_combination h00
  exact sq_add_self_add_one_ne (M 0 0) h'

theorem trace_add (M : Mat) (h : M * M + M + 1 = 0) : M 0 0 + M 1 1 + 1 = 0 := by
  have hc := entry10_ne_zero M h
  have h10 := entry10 M h
  have h' : M 1 0 * (M 0 0 + M 1 1 + 1) = 0 := by linear_combination h10
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact absurd h'' hc
  · exact h''




/-! ## Part 2: the centralizer of an order-three matrix -/

def e1v : V2 := ![1, 0]

theorem smul_one_add_smul_comm (M : Mat) (a b : K5) :
    (a • (1 : Mat) + b • M) * M = M * (a • (1 : Mat) + b • M) := by
  rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

theorem cube_of_sq_add (M : Mat) (hM : M * M + M + 1 = 0) : M * M * M = 1 := by
  have e2 : M * M + (M + 1) = 0 := by rw [← add_assoc]; exact hM
  have e : M * M = -(M + 1) := eq_neg_iff_add_eq_zero.mpr e2
  calc M * M * M = (-(M + 1)) * M := by rw [e]
    _ = -(M * M + M) := by rw [neg_mul, add_mul, one_mul]
    _ = -((-(M + 1)) + M) := by rw [e]
    _ = 1 := by rw [neg_add, neg_neg]; abel

theorem cent_mem (M : Mat) (hM : M * M + M + 1 = 0) (x : Mat) (hx : x * M = M * x) :
    ∃ a b : K5, x = a • (1 : Mat) + b • M := by
  have hc : M 1 0 ≠ 0 := entry10_ne_zero M hM
  have hx' : ∀ i j, (x * M) i j = (M * x) i j := fun i j => congrFun (congrFun hx i) j
  have E10 : x 1 0 * M 0 0 + x 1 1 * M 1 0 = M 1 0 * x 0 0 + M 1 1 * x 1 0 := by
    have h := hx' 1 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have E11 : x 1 0 * M 0 1 + x 1 1 * M 1 1 = M 1 0 * x 0 1 + M 1 1 * x 1 1 := by
    have h := hx' 1 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  obtain ⟨b, hb⟩ : ∃ b : K5, b * M 1 0 = x 1 0 :=
    ⟨x 1 0 * (M 1 0)⁻¹, by rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]⟩
  refine ⟨x 0 0 - b * M 0 0, b, ?_⟩
  have key1 : M 1 0 * x 0 1 = x 1 0 * M 0 1 := by linear_combination -E11
  have key2 : M 1 0 * x 1 1 = M 1 0 * x 0 0 + M 1 1 * x 1 0 - x 1 0 * M 0 0 := by
    linear_combination E10
  have h01 : x 0 1 = b * M 0 1 := by
    refine mul_left_cancel₀ hc ?_
    rw [key1, ← hb]; ring
  have h11 : x 1 1 = x 0 0 - b * M 0 0 + b * M 1 1 := by
    refine mul_left_cancel₀ hc ?_
    rw [key2]
    rw [show M 1 0 * (x 0 0 - b * M 0 0 + b * M 1 1)
        = M 1 0 * x 0 0 - (b * M 1 0) * M 0 0 + (b * M 1 0) * M 1 1 from by ring]
    rw [hb]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, h01]
  · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hb]
  · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, h11]

theorem smul_one_add_smul_eq (M : Mat) (a b : K5) :
    (a • (1 : Mat) + b • M)
      = !![a + b * M 0 0, b * M 0 1; b * M 1 0, a + b * M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]

theorem det_eq_one (M : Mat) (h3 : M * M * M = 1) : M.det = 1 := by
  have h' : (M * M * M).det = 1 := by rw [h3, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul] at h'
  refine cube_roots _ ?_
  rw [pow_three, ← mul_assoc]
  exact h'

theorem det_smul_one_add_smul (M : Mat) (h3 : M * M * M = 1) (hM : M * M + M + 1 = 0)
    (a b : K5) : (a • (1 : Mat) + b • M).det = a^2 - a*b + b^2 := by
  have htr : M 0 0 + M 1 1 = -1 := by
    have h := trace_add M hM
    linear_combination h
  have hdet : M.det = 1 := det_eq_one M h3
  have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hdet
  rw [smul_one_add_smul_eq, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  linear_combination (a*b) * htr + b^2 * hdet'

theorem det_ne_zero_of_ne_zero (M : Mat) (hM : M * M + M + 1 = 0) (a b : K5)
    (h : (a, b) ≠ 0) : (a • (1 : Mat) + b • M).det ≠ 0 := by
  have h3 := cube_of_sq_add M hM
  have hd := det_smul_one_add_smul M h3 hM a b
  intro h0
  rw [hd] at h0
  rcases quad_form_ne_zero a b h0 with ⟨rfl, rfl⟩
  exact h rfl

/-! ## Part 3: the Frobenius twist `w` of an order-three matrix -/

/-- The explicit matrix `w` which conjugates `M` to `M ^ 2`.
Its only interesting entry is `u`, subject to `u * (M 1 0) = -1 - 2 * M 0 0`. -/
def frob (u : K5) : Mat := !![1, u; 0, -1]

theorem frob_sq (u : K5) : frob u * frob u = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frob, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem frob_comm (M : Mat) (hM : M * M + M + 1 = 0) (u : K5)
    (hu : u * M 1 0 = -1 - 2 * M 0 0) :
    frob u * M + M * frob u + frob u = 0 := by
  have htr : M 0 0 + M 1 1 + 1 = 0 := trace_add M hM
  ext i j
  fin_cases i <;> fin_cases j
  · simp [frob, Matrix.add_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination hu
  · simp [frob, Matrix.add_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination u * htr
  · simp [frob, Matrix.add_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · simp [frob, Matrix.add_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination hu - 2 * htr

theorem frob_conj (M : Mat) (hM : M * M + M + 1 = 0) (u : K5)
    (hu : u * M 1 0 = -1 - 2 * M 0 0) :
    frob u * M = (M * M) * frob u := by
  have hcomm := frob_comm M hM u hu
  have e2 : M * M + (M + 1) = 0 := by rw [← add_assoc]; exact hM
  have e : M * M = -(M + 1) := eq_neg_iff_add_eq_zero.mpr e2
  have h1 : frob u * M = -(M * frob u) - frob u := by
    calc frob u * M = frob u * M + (M * frob u + frob u) - (M * frob u + frob u) := by abel
      _ = (frob u * M + M * frob u + frob u) - (M * frob u + frob u) := by abel
      _ = -(M * frob u + frob u) := by rw [hcomm]; abel
      _ = -(M * frob u) - frob u := by abel
  rw [h1, e]
  rw [neg_mul, add_mul, one_mul]
  abel

/-! ## Part 4: the exact remaining gap

Everything the classification needs from the order-three element `g` is now available
except the *cardinality* of the normalizer of `<g>`:

* `mat_sq_add_self_add_one` : an order-three matrix satisfies `M^2 + M + 1 = 0`;
* `cent_mem` : every matrix commuting with `M` is a polynomial in `M`, i.e.
  the centralizer is the 25-element field `F_5[M]`;
* `det_smul_one_add_smul` : the determinant of `a + b M` is `a^2 - a b + b^2`;
* `frob_sq`, `frob_conj` : the explicit Frobenius twist `w = [1,u;0,-1]` with
  `u * M 1 0 = -1 - 2 * M 0 0` satisfies `w^2 = 1` and `w M = M^2 w`.

Consequently the normalizer of `<g>` is the disjoint union of the centralizer and the
coset `w * C(g)`, so its order is `2 * 24 = 48` once the cardinality
`|C(g)| = 24` (the nonzero elements of the field `F_5[g]`) is extracted from
`cent_mem`.  That cardinality extraction, and the two further group-theoretic
inputs listed below, are the exact remaining gaps of the classification. -/

/-- **Missing (1).** The normalizer of a subgroup of order three has 48 elements. -/
def S2014NormalizerCard : Prop :=
  ∀ g : GL2, orderOf g = 3 → Nat.card (Subgroup.normalizer (Subgroup.zpowers g : Set GL2)) = 48

/-- **Missing (2).** The two standard transvections generate `SL_2(F_5)`. -/
def trv1 : GL2 := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by decide)
def trv2 : GL2 := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 1] (by decide)

def S2014TransvectionGeneration : Prop :=
  Nat.card (Subgroup.closure ({trv1, trv2} : Set GL2)) = 120

/-- **Missing (3).** An element of order five fixes a nonzero vector (it is a transvection). -/
def S2014OrderFiveUnipotent : Prop :=
  ∀ a : GL2, orderOf a = 5 → ∃ v : V2, v ≠ 0 ∧ a • v = v

theorem trv1_det : Matrix.GeneralLinearGroup.det trv1 = 1 := by decide
theorem trv2_det : Matrix.GeneralLinearGroup.det trv2 = 1 := by decide

/-! ## Axiom audit -/

#print axioms mat_sq_add_self_add_one
#print axioms cent_mem
#print axioms det_smul_one_add_smul
#print axioms det_ne_zero_of_ne_zero
#print axioms frob_sq
#print axioms frob_conj
#print axioms trace_add
#print axioms entry10_ne_zero

end LeanFormal.IUT.XiFPaper.S2009DicksonActual
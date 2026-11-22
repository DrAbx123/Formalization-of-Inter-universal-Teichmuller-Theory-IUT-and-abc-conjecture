/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open Polynomial
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S1412PsiDivisorActual

/-!
# S1412: the support and degree parts of the divisor identity for `preΨₙ`

For an elliptic Weierstrass curve `W` over an algebraically closed field `F` and an odd
integer `n` with `(n : F) ≠ 0`, the divisor identity for the odd division polynomial is

  `div(preΨₙ(X)) = Σ_{T ∈ W[n]} (T) - n² (O)`

in the standard zero-positive orientation.  Equivalently, in the orientation displayed in
S1397, `n²(O) - Σ_{T ∈ W[n]} (T)` is the negative of this divisor.

Mathlib has no divisor theory for the coordinate ring of `W`.  This file therefore builds
the elementary finite-support integer divisor of the univariate polynomial `preΨₙ`
directly on the point type of `W`:

* at an affine point with abscissa `x` it has the root multiplicity of `x` in `preΨₙ`,
  counted at both points `(x, y)` and `(x, negY x y)` (so a `2`-torsion abscissa receives
  twice the multiplicity at its unique point);
* at the point at infinity it has the pole order `-2 * natDegree (preΨₙ)`.

The two results proved here are exactly the support and degree halves of the divisor
identity:

* `psiDivisor_total`: the total coefficient of `psiDivisor` is `0` (the degree half),
  unconditionally for every nonzero `n`;
* `psiZeroSet_eq_affineTorsion`: if every `n`-torsion point is a zero of `ψₙ` (the forward
  detection direction) and the affine `n`-torsion has `n² - 1` points, then the affine zero
  set of `preΨₙ` is exactly the affine `n`-torsion (the support half).

The second statement is conditional on exactly the two concrete inputs that the tree does
not yet prove for general odd `n`: forward detection and the torsion cardinality.  The
support identity is the divisor route to the reverse direction; the final section records
that these same two inputs therefore give the full conditional zero criterion
`ψₙ(P) = 0 ↔ n • P = 0`.  No use is made of the independent root-criterion computation.

## Main results

* `LeanFormal.IUT.XiFPaper.S1412PsiDivisorActual.exists_nonsingular_of_x`
* `LeanFormal.IUT.XiFPaper.S1412PsiDivisorActual.psiDivisor_total`
* `LeanFormal.IUT.XiFPaper.S1412PsiDivisorActual.psiZeroSet_eq_affineTorsion`
* `LeanFormal.IUT.XiFPaper.S1412PsiDivisorActual.psiDivisor_support_degree`
* `LeanFormal.IUT.XiFPaper.S1412PsiDivisorActual.psiZeroCriterion_of_detection_and_card`

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

-/

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-! ## 1. Points with a prescribed abscissa -/

/-- Every abscissa occurs on an elliptic curve over an algebraically closed field. -/
lemma exists_nonsingular_of_x (x : F) : ∃ y : F, W.Nonsingular x y := by
  classical
  let q : F[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hqdeg : q.degree = 2 := by
    change (X ^ 2 + C (W.a₁ * x + W.a₃) * X -
      C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) : F[X]).degree = 2
    compute_degree!
  have hdeg : q.degree ≠ 0 := by rw [hqdeg]; norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q hdeg
  refine ⟨y, ?_⟩
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W)).mp
  rw [WeierstrassCurve.Affine.equation_iff']
  have hy' : y ^ 2 + (W.a₁ * x + W.a₃) * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa only [q, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.IsRoot.def] using hy
  linear_combination hy'

/-- A chosen nonsingular affine point with the prescribed abscissa. -/
noncomputable def pointOfX (x : F) : W.Point :=
  WeierstrassCurve.Affine.Point.some x
    (Classical.choose (exists_nonsingular_of_x W x))
    (Classical.choose_spec (exists_nonsingular_of_x W x))

lemma pointOfX_nonsingular (x : F) :
    W.Nonsingular x (Classical.choose (exists_nonsingular_of_x W x)) :=
  Classical.choose_spec (exists_nonsingular_of_x W x)

@[simp] lemma pointOfX_x (x : F) : (pointOfX W x).xRep = ![x, 1] := by
  rw [pointOfX, WeierstrassCurve.Affine.Point.xRep_some]

lemma pointOfX_ne_zero (x : F) : pointOfX W x ≠ 0 := by
  rw [pointOfX]
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-! ## 2. The combinatorial divisor of `preΨₙ` -/

/-- The zero-positive divisor of the univariate polynomial `preΨₙ`, as an integer-valued
finitely supported function on `W.Point`.  At infinity the coefficient is the negative pole
order `-2 * natDegree (preΨₙ)`. -/
noncomputable def psiDivisor (n : ℤ) : W.Point →₀ ℤ :=
  (∑ x ∈ (W.preΨ n).roots.toFinset,
    ((W.preΨ n).rootMultiplicity x : ℤ) •
      (Finsupp.single (pointOfX W x) (1 : ℤ) +
        Finsupp.single (-(pointOfX W x)) (1 : ℤ))) -
    (2 * (W.preΨ n).natDegree : ℤ) • Finsupp.single (0 : W.Point) (1 : ℤ)

/-- Total coefficient of a finitely supported integer function. -/
noncomputable def total {α : Type*} (f : α →₀ ℤ) : ℤ :=
  f.sum (fun _ m => m)

@[simp] lemma total_zero {α : Type*} : total (0 : α →₀ ℤ) = 0 := by
  simp [total]

@[simp] lemma total_single {α : Type*} [DecidableEq α] (a : α) (b : ℤ) :
    total (Finsupp.single a b) = b := by
  rw [total, Finsupp.sum_single_index]
  rfl

lemma total_add {α : Type*} (f g : α →₀ ℤ) : total (f + g) = total f + total g := by
  rw [total, Finsupp.sum_add_index']
  · rfl
  · intro a; rfl
  · intro a b c; ring

lemma total_smul {α : Type*} [DecidableEq α] (k : ℤ) (f : α →₀ ℤ) :
    total (k • f) = k * total f := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb hf =>
      rw [smul_add, total_add, hf, total_add]
      have hk : total (k • Finsupp.single a b) = k * b := by
        rw [total, Finsupp.sum_smul_index]
        · simp [Finsupp.sum_single_index]
        · intro i; rfl
      rw [hk, total_single]
      ring

lemma total_neg {α : Type*} [DecidableEq α] (f : α →₀ ℤ) : total (-f) = -total f := by
  have h := total_smul (-1 : ℤ) f
  rwa [neg_one_smul, neg_one_mul] at h

lemma total_sub {α : Type*} [DecidableEq α] (f g : α →₀ ℤ) :
    total (f - g) = total f - total g := by
  rw [sub_eq_add_neg, total_add, total_neg]
  rfl

/-- The total of the affine part of `psiDivisor` is twice the sum of the root
multiplicities. -/
lemma total_psiDivisor_affine (n : ℤ) :
    total (∑ x ∈ (W.preΨ n).roots.toFinset,
      ((W.preΨ n).rootMultiplicity x : ℤ) •
        (Finsupp.single (pointOfX W x) (1 : ℤ) +
          Finsupp.single (-(pointOfX W x)) (1 : ℤ))) =
      2 * ∑ x ∈ (W.preΨ n).roots.toFinset, ((W.preΨ n).rootMultiplicity x : ℤ) := by
  classical
  rw [total, ← Finsupp.sum_finsetSum_index]
  · have hterm : ∀ x ∈ (W.preΨ n).roots.toFinset,
        total (((W.preΨ n).rootMultiplicity x : ℤ) •
          (Finsupp.single (pointOfX W x) (1 : ℤ) +
            Finsupp.single (-(pointOfX W x)) (1 : ℤ))) =
          2 * ((W.preΨ n).rootMultiplicity x : ℤ) := by
      intro x hx
      rw [total_smul]
      rw [total_add, total_single, total_single]
      ring
    calc
      (∑ x ∈ (W.preΨ n).roots.toFinset,
          total (((W.preΨ n).rootMultiplicity x : ℤ) •
            (Finsupp.single (pointOfX W x) (1 : ℤ) +
              Finsupp.single (-(pointOfX W x)) (1 : ℤ))))
          = ∑ x ∈ (W.preΨ n).roots.toFinset,
              2 * ((W.preΨ n).rootMultiplicity x : ℤ) := by
            apply Finset.sum_congr rfl
            exact hterm
      _ = 2 * ∑ x ∈ (W.preΨ n).roots.toFinset,
            ((W.preΨ n).rootMultiplicity x : ℤ) := by
            rw [Finset.mul_sum]
  · intro a; rfl
  · intro a b c; ring

/-- The sum of the root multiplicities of `preΨₙ` is its degree. -/
lemma sum_rootMultiplicity_eq_natDegree (n : ℤ) :
    (∑ x ∈ (W.preΨ n).roots.toFinset, (W.preΨ n).rootMultiplicity x) =
      (W.preΨ n).natDegree := by
  calc
    (∑ x ∈ (W.preΨ n).roots.toFinset, (W.preΨ n).rootMultiplicity x)
        = ∑ x ∈ (W.preΨ n).roots.toFinset, (W.preΨ n).roots.count x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (Polynomial.count_roots (W.preΨ n)).symm
    _ = (W.preΨ n).roots.card := Multiset.toFinset_sum_count_eq _
    _ = (W.preΨ n).natDegree := IsAlgClosed.card_roots_eq_natDegree

/-- The same sum, cast to `ℤ`. -/
lemma sum_rootMultiplicity_eq_natDegree_int (n : ℤ) :
    (∑ x ∈ (W.preΨ n).roots.toFinset, ((W.preΨ n).rootMultiplicity x : ℤ)) =
      ((W.preΨ n).natDegree : ℤ) := by
  rw [← Nat.cast_sum, sum_rootMultiplicity_eq_natDegree]

/-- The degree half of the divisor identity: the total coefficient is zero. -/
theorem psiDivisor_total (n : ℤ) : total (psiDivisor W n) = 0 := by
  classical
  rw [psiDivisor, total_sub, total_smul, total_psiDivisor_affine,
    sum_rootMultiplicity_eq_natDegree_int, total_single]
  ring

/-- The pole order at infinity equals `n.natAbs ^ 2 - 1` for odd `n`. -/
lemma two_mul_natDegree_preΨ (n : ℤ) (hodd : ¬ Even n) (hchar : (n : F) ≠ 0) :
    2 * (W.preΨ n).natDegree = n.natAbs ^ 2 - 1 := by
  rw [W.natDegree_preΨ hchar, if_neg hodd]
  have hoddAbs : Odd n.natAbs := Int.natAbs_odd.mpr (Int.not_even_iff_odd.mp hodd)
  have hoddSq : Odd (n.natAbs ^ 2) := by
    rw [pow_two]
    exact hoddAbs.mul hoddAbs
  have hdvd : 2 ∣ n.natAbs ^ 2 - 1 := (Nat.Odd.sub_odd hoddSq odd_one).two_dvd
  exact Nat.mul_div_cancel' hdvd

lemma roots_card_le_natDegree (n : ℤ) :
    (W.preΨ n).roots.toFinset.card ≤ (W.preΨ n).natDegree :=
  (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)

/-! ## 3. The affine zero set of `preΨₙ` -/

/-- The affine zero set of `preΨₙ`, represented as the two points over each root of
`preΨₙ`.  A `2`-torsion abscissa contributes its unique point only once. -/
noncomputable def psiZeroSet (n : ℤ) : Finset W.Point := by
  classical
  exact (W.preΨ n).roots.toFinset.image (pointOfX W) ∪
    (W.preΨ n).roots.toFinset.image (fun x => -(pointOfX W x))

lemma pointOfX_mem_psiZeroSet {n : ℤ} {x : F} (hx : x ∈ (W.preΨ n).roots.toFinset) :
    pointOfX W x ∈ psiZeroSet W n := by
  classical
  rw [psiZeroSet]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

lemma neg_pointOfX_mem_psiZeroSet {n : ℤ} {x : F}
    (hx : x ∈ (W.preΨ n).roots.toFinset) :
    -(pointOfX W x) ∈ psiZeroSet W n := by
  classical
  rw [psiZeroSet]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

lemma eval_preΨ_eq_zero_of_mem_roots {n : ℤ} (hchar : (n : F) ≠ 0) {x : F}
    (hx : x ∈ (W.preΨ n).roots.toFinset) : (W.preΨ n).eval x = 0 := by
  exact (Polynomial.mem_roots (W.preΨ_ne_zero hchar)).mp (Multiset.mem_toFinset.mp hx)

lemma eval_pointOfX_eq_zero {n : ℤ} (hodd : ¬ Even n) (hchar : (n : F) ≠ 0)
    {x : F} (hx : x ∈ (W.preΨ n).roots.toFinset) :
    W.evalDivisionPolynomialAtPoint n (pointOfX W x) = 0 := by
  rw [pointOfX, WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
    W.evalDivisionPolynomial_eq_eval_preΨ_of_odd (pointOfX_nonsingular W x).1 hodd,
    eval_preΨ_eq_zero_of_mem_roots W hchar hx]

lemma mem_psiZeroSet_iff (n : ℤ) (hodd : ¬ Even n) (hchar : (n : F) ≠ 0)
    (P : W.Point) :
    P ∈ psiZeroSet W n ↔ P ≠ 0 ∧ W.evalDivisionPolynomialAtPoint n P = 0 := by
  classical
  constructor
  · intro hP
    rw [psiZeroSet] at hP
    rcases Finset.mem_union.mp hP with hP | hP
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
      exact ⟨pointOfX_ne_zero W x, eval_pointOfX_eq_zero W hodd hchar hx⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
      refine ⟨neg_ne_zero.mpr (pointOfX_ne_zero W x), ?_⟩
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_neg_of_odd (W := W) hodd]
      exact eval_pointOfX_eq_zero W hodd hchar hx
  · rintro ⟨hP0, hPeval⟩
    cases P with
    | zero => exact absurd rfl hP0
    | some x y hns =>
        have hp : W.preΨ n ≠ 0 := W.preΨ_ne_zero hchar
        have hx : x ∈ (W.preΨ n).roots.toFinset := by
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
          rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
            W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hodd] at hPeval
          exact hPeval
        have hxrep : (WeierstrassCurve.Affine.Point.some x y hns).xRep =
            (pointOfX W x).xRep := by
          rw [WeierstrassCurve.Affine.Point.xRep_some, pointOfX_x]
        rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep with h | h
        · rw [h]
          exact pointOfX_mem_psiZeroSet W hx
        · rw [h]
          exact neg_pointOfX_mem_psiZeroSet W hx

/-- The affine zero set has at most `n.natAbs ^ 2 - 1` points for odd nonzero `n`. -/
lemma psiZeroSet_card_le (n : ℤ) (hodd : ¬ Even n) (hchar : (n : F) ≠ 0) :
    (psiZeroSet W n).card ≤ n.natAbs ^ 2 - 1 := by
  classical
  have hsub : psiZeroSet W n ⊆
      (W.preΨ n).roots.toFinset.image (pointOfX W) ∪
        (W.preΨ n).roots.toFinset.image (fun x => -(pointOfX W x)) := by
    intro P hP
    rw [psiZeroSet] at hP
    exact hP
  calc
    (psiZeroSet W n).card ≤
        ((W.preΨ n).roots.toFinset.image (pointOfX W) ∪
          (W.preΨ n).roots.toFinset.image (fun x => -(pointOfX W x))).card :=
          Finset.card_le_card hsub
    _ ≤ ((W.preΨ n).roots.toFinset.image (pointOfX W)).card +
          ((W.preΨ n).roots.toFinset.image (fun x => -(pointOfX W x))).card :=
          Finset.card_union_le _ _
    _ ≤ (W.preΨ n).roots.toFinset.card + (W.preΨ n).roots.toFinset.card :=
          add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ ≤ (W.preΨ n).natDegree + (W.preΨ n).natDegree :=
          add_le_add (roots_card_le_natDegree W n) (roots_card_le_natDegree W n)
    _ = 2 * (W.preΨ n).natDegree := by ring
    _ = n.natAbs ^ 2 - 1 := two_mul_natDegree_preΨ W n hodd hchar

/-! ## 4. The support half of the divisor identity -/

/-- **Support half.**  Under forward detection and the affine `n`-torsion cardinality, the
affine zero set of `preΨₙ` is exactly the affine `n`-torsion.  This is the support statement
of `div(preΨₙ) = Σ_{T ∈ W[n]} (T) - n²(O)`. -/
theorem psiZeroSet_eq_affineTorsion (n : ℤ) (hodd : ¬ Even n)
    (hchar : (n : F) ≠ 0)
    (hdet : ∀ P : W.Point, n • P = 0 → W.evalDivisionPolynomialAtPoint n P = 0)
    (T : Finset W.Point) (hTcard : T.card = n.natAbs ^ 2)
    (hTmem : ∀ P : W.Point, P ∈ T ↔ n • P = 0) :
    psiZeroSet W n = T.erase 0 := by
  classical
  have h0T : (0 : W.Point) ∈ T := (hTmem 0).mpr (by simp)
  have hTerase : (T.erase 0).card = n.natAbs ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem h0T, hTcard]
  have hsubset : T.erase 0 ⊆ psiZeroSet W n := by
    intro P hP
    rw [Finset.mem_erase] at hP
    obtain ⟨hP0, hPT⟩ := hP
    exact (mem_psiZeroSet_iff W n hodd hchar P).mpr
      ⟨hP0, hdet P ((hTmem P).mp hPT)⟩
  have hcard : (psiZeroSet W n).card ≤ (T.erase 0).card := by
    rw [hTerase]
    exact psiZeroSet_card_le W n hodd hchar
  exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

/-! ## 5. The packaged support/degree theorem -/

/-- **Support and degree parts of the divisor identity.**  The affine zero set of `preΨₙ` is
the affine `n`-torsion (support), and the total coefficient of `psiDivisor` is zero (degree),
matching the degree `#W[n] - n² = 0` of the standard right-hand side
`Σ_{T ∈ W[n]} (T) - n²(O)` (and hence also its negative orientation in S1397). -/
theorem psiDivisor_support_degree (n : ℤ) (hodd : ¬ Even n)
    (hchar : (n : F) ≠ 0)
    (hdet : ∀ P : W.Point, n • P = 0 → W.evalDivisionPolynomialAtPoint n P = 0)
    (T : Finset W.Point) (hTcard : T.card = n.natAbs ^ 2)
    (hTmem : ∀ P : W.Point, P ∈ T ↔ n • P = 0) :
    psiZeroSet W n = T.erase 0 ∧
    total (psiDivisor W n) = 0 ∧
    total (psiDivisor W n) = (T.card : ℤ) - ((n.natAbs ^ 2 : ℕ) : ℤ) ∧
    (∀ P : W.Point, P ∈ psiZeroSet W n ↔
      P ≠ 0 ∧ W.evalDivisionPolynomialAtPoint n P = 0) := by
  refine ⟨psiZeroSet_eq_affineTorsion W n hodd hchar hdet T hTcard hTmem,
    psiDivisor_total W n, ?_, ?_⟩
  · rw [psiDivisor_total, hTcard]
    ring
  · intro P
    exact mem_psiZeroSet_iff W n hodd hchar P

/-! ## 6. The conditional zero criterion obtained from the support identity -/

/-- **Conditional zero criterion from the divisor support identity.**  This is the divisor
route, not the independent `ψₙ(P) = 0 → n • P = 0` computation: forward detection supplies
`W[n] ⊆ {ψₙ = 0}` and the torsion cardinality supplies the matching count, so the support
equality of the divisor identity forces the reverse inclusion. -/
theorem psiZeroCriterion_of_detection_and_card (n : ℤ) (hodd : ¬ Even n)
    (hchar : (n : F) ≠ 0)
    (hdet : ∀ P : W.Point, n • P = 0 → W.evalDivisionPolynomialAtPoint n P = 0)
    (T : Finset W.Point) (hTcard : T.card = n.natAbs ^ 2)
    (hTmem : ∀ P : W.Point, P ∈ T ↔ n • P = 0) :
    ∀ P : W.Point, n • P = 0 ↔ W.evalDivisionPolynomialAtPoint n P = 0 := by
  have hsupp : psiZeroSet W n = T.erase 0 :=
    psiZeroSet_eq_affineTorsion W n hodd hchar hdet T hTcard hTmem
  intro P
  constructor
  · exact hdet P
  · intro hP
    by_cases hP0 : P = 0
    · rw [hP0]
      simp
    · have hmem : P ∈ psiZeroSet W n :=
        (mem_psiZeroSet_iff W n hodd hchar P).mpr ⟨hP0, hP⟩
      rw [hsupp] at hmem
      exact (hTmem P).mp (Finset.mem_of_mem_erase hmem)

/-! ## 7. Axiom footprint -/

#print axioms exists_nonsingular_of_x
#print axioms psiDivisor_total
#print axioms psiZeroSet_eq_affineTorsion
#print axioms psiDivisor_support_degree
#print axioms psiZeroCriterion_of_detection_and_card

end LeanFormal.IUT.XiFPaper.S1412PsiDivisorActual
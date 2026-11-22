/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

/-!
# Cardinality of the odd division-polynomial locus

Let `K` be a field and `W` a Weierstrass curve over `K`.  The mathematical prerequisite for the
dimension-two matrix Galois representation `ρ_{W,p} : Gal(K̄/K) → GL₂(𝔽_p)` of the Frey chain is
that the `p`-torsion of `W` has `p²` elements: one point at infinity and `p² - 1` affine points,
whose `x`-coordinates are roots of the odd `p`-division polynomial `preΨ_p` of degree `(p²-1)/2`,
two points lying over each root.

Mathlib does **not** contain the group-law correspondence `p • P = 0 ↔ ψ_p(P) = 0`, so the equality
`#W[p] = p²` cannot be proved from the library, and no separability or basis hypothesis is
available either.  What *is* available, and what this file establishes, are the honest cardinality
bounds that make up the `≤ p²` half of that prerequisite:

* `card_le_of_eval_preΨ_eq_zero`: at most `(n²-1)/2` distinct `x`-coordinates satisfy
  `preΨₙ x = 0`, for odd `n` with `(n : K) ≠ 0` (no separability assumed);
* `card_roots_preΨ_le`, `card_roots_ΨSq_le`, `card_roots_Φ_le`: the corresponding bounds for the
  root multisets, valid with no characteristic hypothesis;
* `card_le_of_evalDivisionPolynomialAtPoint_eq_zero`: any finite set of nonzero points at which
  the odd `n`-division polynomial `ψₙ` vanishes has at most `n² - 1` elements, since over each root
  there are at most two points, namely `P` and `-P`;
* `card_le_of_prime_divisionLocus`: the prime form, `≤ p² - 1` for an odd prime `p`.

Adding the point at infinity gives the bound `p²` for the full division locus.  The identification
of this locus with the `nsmul`-torsion subgroup `{P | p • P = 0}` is exactly the missing library
statement and is deliberately *not* assumed.

## Main statements

* `WeierstrassCurve.card_le_of_eval_preΨ_eq_zero`
* `WeierstrassCurve.card_roots_preΨ_le`
* `WeierstrassCurve.card_le_of_evalDivisionPolynomialAtPoint_eq_zero`
* `WeierstrassCurve.card_le_of_prime_divisionLocus`

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point, cardinality
-/

open Polynomial
open scoped Polynomial.Bivariate

universe u

namespace WeierstrassCurve

section Cardinality

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

/-- **The `x`-coordinates of odd `n`-division points.**
For an odd integer `n` with `(n : K) ≠ 0`, at most `(n²-1)/2` distinct elements of `K` are roots of
the odd `n`-division polynomial `preΨₙ`.  No separability of `preΨₙ` is assumed: the bound only uses
its degree, which is available unconditionally in the library. -/
theorem card_le_of_eval_preΨ_eq_zero {n : ℤ} (hn : ¬ Even n) (hchar : (n : K) ≠ 0)
    (Z : Finset K) (hZ : ∀ x ∈ Z, (W.preΨ n).eval x = 0) :
    Z.card ≤ (n.natAbs ^ 2 - 1) / 2 := by
  have hle : Z.card ≤ (W.preΨ n).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    rw [Polynomial.mem_roots (W.preΨ_ne_zero hchar), Polynomial.IsRoot.def]
    exact hZ x (by simpa using hx)
  calc Z.card ≤ (W.preΨ n).natDegree := hle
    _ ≤ (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 := W.natDegree_preΨ_le n
    _ = (n.natAbs ^ 2 - 1) / 2 := by rw [if_neg hn]

/-- The root multiset of the odd `n`-division polynomial `preΨₙ` has at most `(n²-1)/2` elements.
No characteristic hypothesis is needed here. -/
theorem card_roots_preΨ_le {n : ℤ} (hn : ¬ Even n) :
    (W.preΨ n).roots.card ≤ (n.natAbs ^ 2 - 1) / 2 := by
  calc (W.preΨ n).roots.card ≤ (W.preΨ n).natDegree := Polynomial.card_roots' _
    _ ≤ (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 := W.natDegree_preΨ_le n
    _ = (n.natAbs ^ 2 - 1) / 2 := by rw [if_neg hn]

/-- **The `x`-coordinates cut out by `ΨSqₙ`.**
For `(n : K) ≠ 0`, at most `n² - 1` distinct elements of `K` are roots of `ΨSqₙ`. -/
theorem card_le_of_eval_ΨSq_eq_zero (n : ℤ) (hchar : (n : K) ≠ 0)
    (Z : Finset K) (hZ : ∀ x ∈ Z, (W.ΨSq n).eval x = 0) :
    Z.card ≤ n.natAbs ^ 2 - 1 := by
  have hle : Z.card ≤ (W.ΨSq n).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    rw [Polynomial.mem_roots (W.ΨSq_ne_zero hchar), Polynomial.IsRoot.def]
    exact hZ x (by simpa using hx)
  calc Z.card ≤ (W.ΨSq n).natDegree := hle
    _ ≤ n.natAbs ^ 2 - 1 := W.natDegree_ΨSq_le n

/-- The root multiset of `ΨSqₙ` has at most `n² - 1` elements. -/
theorem card_roots_ΨSq_le (n : ℤ) : (W.ΨSq n).roots.card ≤ n.natAbs ^ 2 - 1 := by
  calc (W.ΨSq n).roots.card ≤ (W.ΨSq n).natDegree := Polynomial.card_roots' _
    _ ≤ n.natAbs ^ 2 - 1 := W.natDegree_ΨSq_le n

/-- **The `x`-coordinates cut out by `Φₙ`.**
At most `n²` distinct elements of `K` are roots of the polynomial `Φₙ`. -/
theorem card_le_of_eval_Φ_eq_zero (n : ℤ)
    (Z : Finset K) (hZ : ∀ x ∈ Z, (W.Φ n).eval x = 0) :
    Z.card ≤ n.natAbs ^ 2 := by
  have hle : Z.card ≤ (W.Φ n).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    rw [Polynomial.mem_roots (W.Φ_ne_zero n), Polynomial.IsRoot.def]
    exact hZ x (by simpa using hx)
  calc Z.card ≤ (W.Φ n).natDegree := hle
    _ ≤ n.natAbs ^ 2 := W.natDegree_Φ_le n

/-- The root multiset of `Φₙ` has at most `n²` elements. -/
theorem card_roots_Φ_le (n : ℤ) : (W.Φ n).roots.card ≤ n.natAbs ^ 2 := by
  calc (W.Φ n).roots.card ≤ (W.Φ n).natDegree := Polynomial.card_roots' _
    _ ≤ n.natAbs ^ 2 := W.natDegree_Φ_le n

/-- An element of an additive group all of whose pairs satisfy `P = Q` or `P = -Q` belongs to a
set with at most two elements. -/
private lemma card_le_two_of_forall_eq_or_eq_neg {G : Type*} [AddGroup G]
    {s : Finset G} (h : ∀ P ∈ s, ∀ Q ∈ s, P = Q ∨ P = -Q) : s.card ≤ 2 := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨P, hP⟩
  · simp
  · have hsub : s ⊆ {P, -P} := by
      intro Q hQ
      rcases h P hP Q hQ with hPQ | hPneg
      · exact Finset.mem_insert.mpr (Or.inl hPQ.symm)
      · refine Finset.mem_insert.mpr (Or.inr ?_)
        rw [Finset.mem_singleton]
        rw [hPneg, neg_neg]
    calc s.card ≤ ({P, -P} : Finset G).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

/-- **Cardinality of the odd division-polynomial locus.**
For an odd integer `n` with `(n : K) ≠ 0`, any finite set `S` of nonzero points at which the
`n`-division polynomial vanishes has at most `n² - 1` elements.  The points over a fixed root of
`preΨₙ` are at most the two opposite points `P` and `-P`, and the roots number at most `(n²-1)/2`,
giving the bound `2 · (n²-1)/2 ≤ n² - 1`.

This is the honest `≤ p²` half of the odd-prime torsion cardinality prerequisite; the equality
`# {P | p • P = 0} = p²` requires the group-law correspondence with division polynomials, which is
not present in Mathlib and is not assumed. -/
theorem card_le_of_evalDivisionPolynomialAtPoint_eq_zero {n : ℤ} (hn : ¬ Even n)
    (hchar : (n : K) ≠ 0) (S : Finset W.toAffine.Point)
    (hS : ∀ P ∈ S, P ≠ 0 ∧ W.evalDivisionPolynomialAtPoint n P = 0) :
    S.card ≤ n.natAbs ^ 2 - 1 := by
  classical
  have hfib : ∀ a : K, (S.filter (fun P => P.xRep 0 = a)).card ≤ 2 := by
    intro a
    refine card_le_two_of_forall_eq_or_eq_neg ?_
    intro P hP Q hQ
    rw [Finset.mem_filter] at hP hQ
    have hPne : P ≠ 0 := (hS P hP.1).1
    have hQne : Q ≠ 0 := (hS Q hQ.1).1
    rcases P with _ | ⟨x, y, hPns⟩
    · exact absurd rfl hPne
    rcases Q with _ | ⟨x', y', hQns⟩
    · exact absurd rfl hQne
    have hxeq : x = x' := by
      have h1 : x = a := by simpa [WeierstrassCurve.Affine.Point.xRep_some] using hP.2
      have h2 : x' = a := by simpa [WeierstrassCurve.Affine.Point.xRep_some] using hQ.2
      rw [h1, h2]
    exact (WeierstrassCurve.Affine.Point.X_eq_iff).mp hxeq
  have himage : (S.image (fun P : W.toAffine.Point => P.xRep 0)).card ≤
      (W.preΨ n).roots.card := by
    have hsub : S.image (fun P : W.toAffine.Point => P.xRep 0) ⊆
        (W.preΨ n).roots.toFinset := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨P, hP, rfl⟩ := ha
      have hPne : P ≠ 0 := (hS P hP).1
      have hPzero : W.evalDivisionPolynomialAtPoint n P = 0 := (hS P hP).2
      rcases P with _ | ⟨x, y, hPns⟩
      · exact absurd rfl hPne
      · have hxval : (WeierstrassCurve.Affine.Point.some x y hPns).xRep 0 = x := by
          rw [WeierstrassCurve.Affine.Point.xRep_some]
          simp
        rw [hxval, Multiset.mem_toFinset,
          Polynomial.mem_roots (W.preΨ_ne_zero hchar), Polynomial.IsRoot.def]
        rw [← W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hPns.1 hn]
        simpa using hPzero
    calc (S.image (fun P : W.toAffine.Point => P.xRep 0)).card
        ≤ ((W.preΨ n).roots.toFinset).card := Finset.card_le_card hsub
      _ ≤ (W.preΨ n).roots.card := Multiset.toFinset_card_le _
  calc S.card ≤ 2 * (S.image (fun P : W.toAffine.Point => P.xRep 0)).card :=
        Finset.card_le_mul_card_image (f := fun P : W.toAffine.Point => P.xRep 0) S 2
          (fun b _ => hfib b)
    _ ≤ 2 * (W.preΨ n).roots.card := Nat.mul_le_mul_left 2 himage
    _ ≤ 2 * ((n.natAbs ^ 2 - 1) / 2) := Nat.mul_le_mul_left 2 (card_roots_preΨ_le W hn)
    _ ≤ n.natAbs ^ 2 - 1 := Nat.mul_div_le (n.natAbs ^ 2 - 1) 2

/-- **Prime form of the odd division-polynomial locus bound.**
For an odd prime `p` with `(p : K) ≠ 0`, any finite set of nonzero points at which the
`p`-division polynomial vanishes has at most `p² - 1` elements; together with the point at infinity
this is the bound `p²` for the `p`-division locus. -/
theorem card_le_of_prime_divisionLocus {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hchar : (p : K) ≠ 0) (S : Finset W.toAffine.Point)
    (hS : ∀ P ∈ S, P ≠ 0 ∧ W.evalDivisionPolynomialAtPoint (p : ℤ) P = 0) :
    S.card ≤ p ^ 2 - 1 := by
  have hnotEven : ¬ Even (p : ℤ) := by
    rw [Int.even_coe_nat]
    exact Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two hodd)
  have hchar' : ((p : ℤ) : K) ≠ 0 := by simpa using hchar
  have hcard := W.card_le_of_evalDivisionPolynomialAtPoint_eq_zero hnotEven hchar' S hS
  simpa [Int.natAbs_natCast] using hcard

/-- **Prime form including the point at infinity.**
For an odd prime `p` with `(p : K) ≠ 0`, any finite set of points each of which is either the point
at infinity or a nonzero point at which the `p`-division polynomial vanishes has at most `p²`
elements.  This is the honest upper bound matching the expected order `p²` of the `p`-torsion. -/
theorem card_le_of_prime_divisionLocus_with_zero {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hchar : (p : K) ≠ 0) (S : Finset W.toAffine.Point)
    (hS : ∀ P ∈ S, P = 0 ∨ (P ≠ 0 ∧ W.evalDivisionPolynomialAtPoint (p : ℤ) P = 0)) :
    S.card ≤ p ^ 2 := by
  classical
  have herase : ∀ P ∈ S.erase 0, P ≠ 0 ∧ W.evalDivisionPolynomialAtPoint (p : ℤ) P = 0 := by
    intro P hP
    rw [Finset.mem_erase] at hP
    rcases hS P hP.2 with hzero | h
    · exact absurd hzero hP.1
    · exact h
  have hbound : (S.erase 0).card ≤ p ^ 2 - 1 :=
    W.card_le_of_prime_divisionLocus hp hodd hchar (S.erase 0) herase
  have hsub : S ⊆ insert (0 : W.toAffine.Point) (S.erase 0) := by
    intro P hP
    by_cases hP0 : P = 0
    · exact Finset.mem_insert.mpr (Or.inl hP0)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hP0, hP⟩))
  calc S.card ≤ (insert (0 : W.toAffine.Point) (S.erase 0)).card := Finset.card_le_card hsub
    _ ≤ (S.erase 0).card + 1 := Finset.card_insert_le _ _
    _ ≤ (p ^ 2 - 1) + 1 := Nat.add_le_add_right hbound 1
    _ = p ^ 2 := by
        rw [Nat.sub_add_cancel]
        exact Nat.succ_le_of_lt (pow_pos hp.pos 2)

end Cardinality

end WeierstrassCurve

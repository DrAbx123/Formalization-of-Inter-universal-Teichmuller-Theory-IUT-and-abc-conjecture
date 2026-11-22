/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import tmp.sheaf.xif.paper.S1999S1993BridgeActual

/-!
# S2003: the splitting field of S1687P contains no square root of -1

Let `P = S1687P` (the residual cubic of the 3-division polynomial, S1687) and let

  `K = S1993KP = SplittingField P`.

S1993 proved that `K / Q` is finite Galois with `[K : Q] = 6`, that `Gal(K/Q)` is
the full symmetric group on the three roots of `P`, and that `K` contains an explicit
square root `S1993SqrtNegThree` of `-3`.  S1999 proved the splitting-field bridge
`S1687Field ~= K` and the auxiliary facts

* `S1999_mem_adjoin_s` : the normal form `a + b * sqrt(-3)` for `Q(sqrt(-3))`,
* `S1999_no_sqrt_neg_one_in_adjoin_s` : `Q(sqrt(-3))` contains no square root of `-1`,
* `S1999_minpoly_of_sq_eq_neg_one` : a square root of `-1` has minimal polynomial
  `X^2 + 1` (hence degree 2),

and isolated the exact remaining missing statement

  `S1999KNoSqrtNegOne : forall x : K, x^2 != -1`

(equivalently `K` does not contain `Q(i)`, equivalently `K` and `Q(i)` are linearly
disjoint over `Q`), together with the reduction
`S1999KNoSqrtNegOne_of_quadraticSubfieldUnique` from the uniqueness of the quadratic
subfield of `K`.  **This file proves `S1999KNoSqrtNegOne`, and, in the same stroke,
the uniqueness `S1999QuadraticSubfieldUnique` of the quadratic subfield of `K`.**

## The argument

The proof is a degree count in `K`, and avoids both the discriminant plumbing
(S1993 already carries the explicit `sqrt(-3)`) and the Galois correspondence
(the abstract statement that `S_3` has a unique index-2 subgroup `A_3`).

Given `x` in `K` with `x^2 = -1`, the field `L = Q(x)` is a second quadratic
subfield of `K`:

* `L = Q(x)` has degree `2` over `Q` because `minpoly Q x = X^2 + 1`;
* `L != Q(sqrt(-3))`, because `Q(sqrt(-3))` contains no square root of `-1`.

Now let `B = Q(sqrt(-3))` and `M = L sup B`.  Then

1. `[M : Q] <= [L : Q] * [B : Q] = 4`  (`IntermediateField.finrank_sup_le`);
2. `[L : Q] = 2` divides `[M : Q]`      (`IntermediateField.finrank_dvd_of_le_right`);
3. `[M : Q] != 2`: otherwise `L = M` (equal degree inclusion), hence `B <= L` and so
   `B = L`, contradicting `L != B`;
4. hence `[M : Q] = 4`.

But `Q <= M <= K` is a tower of finite extensions, so `[K : Q] = [K : M] * [M : Q]`,
i.e. `6 = [K : M] * 4`, which is impossible.  This is
`S2003_finrank_sup_of_ne` plus the tower law.

Applying the same argument to an arbitrary quadratic subfield `L` of `K` shows that
`L` must be `Q(sqrt(-3))` (`S2003QuadraticSubfieldUnique`): the only quadratic
subfield of `K` is the one cut out by `A_3 <= Gal(K/Q) ~= S_3`.

## Consequences (for the next file on `F' = SplittingField (S1687H * (X^2+1))`)

* `K` contains no square root of `-1`, i.e. `K` does not contain `Q(i)`;
* the unique quadratic subfield of `K` is `Q(sqrt(-3))`;
* hence `K` and `Q(i)` are linearly disjoint over `Q`, so the compositum `K * Q(i)`
  (inside `F' = SplittingField (S1687H * (X^2+1))`) has degree `6 * 2 = 12` over `Q`,
  `Gal(F'/Q) ~= S_3 x C_2`, and the three quadratic subfields of `F'` are
  `Q(sqrt(-3))`, `Q(sqrt(3))` and `Q(i)`.
  These statements live in the `F'`-file (S1720/S1722 interface); the input they need
  from `K` is exactly `S2003KNoSqrtNegOne` proved here.

## Verification status

The file compiles (EXIT 0) with no sorry, admit, axiom, opaque declaration or
native_decide; the axiom footprint of the main theorems is `propext`,
`Classical.choice` and `Quot.sound` only (see the `#print axioms` block at the end).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2003KNoSqrtNegOneActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1722DegreePrimeActual
open LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual
open LeanFormal.IUT.XiFPaper.S1999S1993BridgeActual
open scoped IntermediateField

/-! ## 1. Two distinct quadratic subfields of `K` generate a degree-4 subfield -/

/-- **Degree count.**  Two distinct quadratic subfields `L`, `M` of `K` have a
compositum of degree `4` over `Q`.  This is the field-theoretic core of the
"unique quadratic subfield" statement: the compositum cannot have degree `2`,
cannot exceed `4`, and its degree is a multiple of `2`. -/
theorem S2003_finrank_sup_of_ne {L M : IntermediateField ℚ S1993KP}
    (hL : Module.finrank ℚ L = 2) (hM : Module.finrank ℚ M = 2) (hne : L ≠ M) :
    Module.finrank ℚ ↥(L ⊔ M) = 4 := by
  -- Upper bound: `[L sup M : Q] <= [L : Q] * [M : Q] = 4`.
  have hle : Module.finrank ℚ ↥(L ⊔ M) ≤ 4 := by
    have h := IntermediateField.finrank_sup_le (K := ℚ) L M
    rw [hL, hM] at h
    simpa using h
  -- Divisibility: `[L : Q] = 2` divides `[L sup M : Q]`.
  have hdvd : 2 ∣ Module.finrank ℚ ↥(L ⊔ M) := by
    have h := IntermediateField.finrank_dvd_of_le_right (F := L) (E := L ⊔ M) le_sup_left
    rwa [hL] at h
  -- `[L sup M : Q]` is not `2`, since that would force `L = L sup M`, hence `L = M`.
  have hne2 : Module.finrank ℚ ↥(L ⊔ M) ≠ 2 := by
    intro h2
    have hLM : L = L ⊔ M := by
      refine IntermediateField.eq_of_le_of_finrank_eq le_sup_left ?_
      rw [h2, hL]
    have hML : M ≤ L := by
      rw [hLM]
      exact le_sup_right
    have hML' : M = L :=
      IntermediateField.eq_of_le_of_finrank_eq hML (by rw [hM, hL])
    exact hne hML'.symm
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Module.finrank ℚ ↥(L ⊔ M) := Module.finrank_pos
  omega

/-- A degree-count form: two distinct quadratic subfields of `K` cannot coexist,
because their compositum has degree `4` while `[K : Q] = 6`. -/
theorem S2003_not_two_quadratic {L M : IntermediateField ℚ S1993KP}
    (hL : Module.finrank ℚ L = 2) (hM : Module.finrank ℚ M = 2) (hne : L ≠ M) : False := by
  have h4 : Module.finrank ℚ ↥(L ⊔ M) = 4 := S2003_finrank_sup_of_ne hL hM hne
  have htower : Module.finrank ℚ ↥(L ⊔ M) * Module.finrank ↥(L ⊔ M) S1993KP
      = Module.finrank ℚ S1993KP :=
    Module.finrank_mul_finrank ℚ ↥(L ⊔ M) S1993KP
  rw [h4, S1993_finrank_K] at htower
  omega

/-! ## 2. The exact remaining missing of S1999 -/

/-- **`K` has no square root of `-1`.**  This is the statement
`S1999KNoSqrtNegOne` isolated by S1999 as the exact missing input for
`[F' : Q] = 12`, `Gal(F'/Q) ~= S_3 x C_2` and the classification of the quadratic
subfields of `F' = SplittingField (S1687H * (X^2 + 1))`. -/
theorem S2003KNoSqrtNegOne : S1999KNoSqrtNegOne := by
  intro x hx
  have hxint : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
  -- `Q(x)` is a quadratic subfield of `K`.
  have hL2 : Module.finrank ℚ (ℚ⟮x⟯ : IntermediateField ℚ S1993KP) = 2 := by
    rw [IntermediateField.adjoin.finrank hxint, S1999_minpoly_of_sq_eq_neg_one x hx]
    exact Polynomial.natDegree_eq_of_degree_eq_some (by compute_degree!)
  -- It is not `Q(sqrt(-3))`, since the latter has no square root of `-1`.
  have hne : (ℚ⟮x⟯ : IntermediateField ℚ S1993KP) ≠ ℚ⟮S1993SqrtNegThree⟯ := by
    intro h
    have hxB : x ∈ (ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP) := by
      rw [← h]
      exact IntermediateField.mem_adjoin_simple_self ℚ x
    exact S1999_no_sqrt_neg_one_in_adjoin_s x hxB hx
  exact S2003_not_two_quadratic hL2 S1993_adjoin_s_finrank hne

/-- The same statement without reference to the named `Prop` of S1999. -/
theorem S2003_sq_ne_neg_one (x : S1993KP) : x ^ 2 ≠ -1 :=
  S2003KNoSqrtNegOne x

/-! ## 3. The quadratic subfield of `K` is unique

This is `S1999QuadraticSubfieldUnique`, the second form of the missing input used by
S1999's reduction `S1999KNoSqrtNegOne_of_quadraticSubfieldUnique`.  It is the
Galois-theoretic statement that `A_3` is the only index-2 subgroup of
`Gal(K/Q) ~= S_3`, proved here by the same degree count. -/

/-- **The only quadratic subfield of `K` is `Q(sqrt(-3))`.** -/
theorem S2003QuadraticSubfieldUnique : S1999QuadraticSubfieldUnique := by
  intro L hL
  by_contra hne
  exact S2003_not_two_quadratic hL S1993_adjoin_s_finrank hne

/-- Cross-check: S1999's reduction, fed with the uniqueness proved here, reproduces
the main theorem (both routes agree). -/
theorem S2003KNoSqrtNegOne_via_unique : S1999KNoSqrtNegOne :=
  S1999KNoSqrtNegOne_of_quadraticSubfieldUnique S2003QuadraticSubfieldUnique

/-! ## 4. Axiom audit -/

#print axioms S2003_finrank_sup_of_ne
#print axioms S2003_not_two_quadratic
#print axioms S2003KNoSqrtNegOne
#print axioms S2003QuadraticSubfieldUnique
#print axioms S2003KNoSqrtNegOne_via_unique

end LeanFormal.IUT.XiFPaper.S2003KNoSqrtNegOneActual

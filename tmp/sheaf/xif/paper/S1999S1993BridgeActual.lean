/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import tmp.sheaf.xif.paper.S1993D5FiniteGroupBridgeActual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# S1999: the actual bridge from S1993 to the splitting field of S1687H

S1993 proved the S_3 structure of K = SplittingField S1687P but recorded the
splitting-field bridge

  S1993SplittingFieldH_eq : Nonempty (S1687Field ~= SplittingField S1687P)

as its exact first missing.  This file proves that bridge.

The mathematical content is the explicit square-root certificate of S1993:
for every root t of P in K there is y in K with y^2 = t, namely
y = B(t) * sqrt(-3), because B(t)^2 = -t/3 (S1993B_sq) and sqrt(-3)^2 = -3.

Consequently

* H = P(X^2) splits in K (each X^2 - C t factors as (X - C y)(X + C y)),
* K is generated over Q by the roots of H: the root rho = B(alpha)sqrt(-3) of H
  gives alpha = rho^2, hence B(alpha) = aeval alpha B lies in the generated
  field, and then sqrt(-3) = rho / B(alpha) lies in it as well; together with
  K = Q(alpha, sqrt(-3)) (S1993_sup_eq_top) this gives generation.

Hence K is a splitting field of S1687H, and Mathlib's
Polynomial.IsSplittingField.algEquiv produces the required Q-algebra
equivalence.  Consequences: [S1687Field : Q] = 6, Gal(S1687H/Q) ~= S_3 as a
permutation group on the three roots of P, and #Gal(S1687H/Q) = 6 (section 8).

## The next missing, and what is proved towards it (sections 7-8)

The remaining F'-block of S1993 (S1993FprimeGroupStructure, the classification
S1993QuadraticSubfields, and [F' : Q] = 12, where F' = S1720Field =
SplittingField (S1687H * (X^2+1))) has a single obstruction in K:

  S1999KNoSqrtNegOne :  forall x in K, x^2 is not -1,

equivalently K does not contain Q(i), equivalently K and Q(i) are linearly
disjoint over Q.  Given that statement, F' = SplittingField(S1687H * (X^2+1))
is the compositum of a copy of K (degree 6) and Q(i) (degree 2), so
[F' : Q] = 12 and Gal(F'/Q) ~= Gal(S1687H/Q) x Gal(Q(i)/Q) via
Polynomial.Gal.restrictProd plus the cardinality count 6 * 2 = 12; the three
quadratic subfields of F' are then Q(sqrt(-3)), Q(sqrt(3)) and Q(i).

What is proved here towards that statement:

* S1999_mem_adjoin_s: every element of Q(sqrt(-3)) is a + b * sqrt(-3) with
  a, b rational (explicit normal form, via division by X^2 + 3);
* S1999_no_sqrt_neg_one_in_adjoin_s: Q(sqrt(-3)) contains no square root of -1
  (the two branches a = 0 and b = 0 are ruled out by
  S1999_sq_ne_three : 3 is not a rational square, and by a^2 >= 0);
* S1999_minpoly_of_sq_eq_neg_one: a square root of -1 has minimal polynomial
  X^2 + 1, hence degree 2;
* S1999KNoSqrtNegOne_of_quadraticSubfieldUnique: if the quadratic subfield of K
  is unique (i.e. every degree-2 IntermediateField of K is Q(sqrt(-3))), then K
  has no square root of -1.

The missing step is exactly the uniqueness of the quadratic subfield of K (or,
equivalently, S1999KNoSqrtNegOne): one must exclude a compositum
Q(sqrt(-3)) + Q(x) of degree 3 (or 4) inside the degree-6 field K, which is the
statement that the only quadratic subfield of K is the discriminant field
Q(sqrt(-3)) cut out by A_3 in Gal(K/Q) ~= S_3.

## Verification status

The file compiles (EXIT 0) with no sorry, admit, axiom, opaque declaration or
native_decide.  The axiom footprint of every main theorem is propext,
Classical.choice and Quot.sound only; see the #print axioms block at the end.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1999S1993BridgeActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1722DegreePrimeActual
open LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual
open scoped IntermediateField

/-! ## 1. General splitting lemmas -/

/-- Composition with X ^ 2 distributes over finite products. -/
theorem S1999_multiset_prod_comp {L : Type*} [CommSemiring L] (m : Multiset L[X]) (q : L[X]) :
    (m.prod).comp q = (m.map (fun f => f.comp q)).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, mul_comp, ih]

/-- If a polynomial splits and every one of its roots is a square, then its
composition with X ^ 2 splits. -/
theorem S1999_splits_comp_X_sq {L : Type*} [Field L] {f : L[X]} (hf : f.Splits)
    (h : ∀ t ∈ f.roots, ∃ y : L, y ^ 2 = t) : (f.comp (X ^ 2)).Splits := by
  have hprod : f.comp (X ^ 2)
      = C f.leadingCoeff * (f.roots.map fun t => (X - C t).comp (X ^ 2)).prod := by
    conv_lhs => rw [hf.eq_prod_roots]
    rw [mul_comp, C_comp, S1999_multiset_prod_comp, Multiset.map_map]
    rfl
  rw [hprod]
  refine Splits.mul (Splits.C _) (Splits.multisetProd ?_)
  intro g hg
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hg
  obtain ⟨y, hy⟩ := h t ht
  have hfac : (X - C t).comp (X ^ 2) = (X - C y) * (X + C y) := by
    have hy' : y * y = t := by rw [← pow_two]; exact hy
    have h1 : (X - C y) * (X + C y) = X ^ 2 - C t := by
      calc (X - C y) * (X + C y) = X ^ 2 - C y * C y := by ring
        _ = X ^ 2 - C (y * y) := by rw [C_mul]
        _ = X ^ 2 - C t := by rw [hy']
    rw [h1, sub_comp, X_comp, C_comp]
  rw [hfac]
  exact Splits.mul (Splits.X_sub_C y) (Splits.X_add_C y)

/-! ## 2. Square roots of the roots of S1687P in K -/

/-- Every root of S1687P in K is a square: B(t) * sqrt(-3) is a square root of t. -/
theorem S1999_root_isSquare (t : S1993KP) (ht : aeval t S1687P = 0) :
    ∃ y : S1993KP, y ^ 2 = t := by
  refine ⟨aeval t S1993B * S1993SqrtNegThree, ?_⟩
  rw [mul_pow, S1993B_sq t ht, S1993SqrtNegThree_sq]
  have h : -(t / 3) * (-3 : S1993KP) = t := by
    field_simp
  exact h

/-- alpha is a nonzero element of K. -/
theorem S1999Alpha_ne_zero : S1993Alpha ≠ 0 := by
  intro h0
  have h := S1993Alpha_root
  rw [h0] at h
  have h' : algebraMap ℚ S1993KP (6153500390625 : ℚ) = 0 := by
    simpa [S1687P] using h
  have hq : (6153500390625 : ℚ) = 0 := (algebraMap ℚ S1993KP).injective (by simpa using h')
  norm_num at hq

/-! ## 3. S1687H splits in K -/

/-- S1687H = S1687P.comp (X ^ 2) transported to any Q-algebra. -/
theorem S1999H_map_eq (K : Type*) [Field K] [Algebra ℚ K] :
    S1687H.map (algebraMap ℚ K)
      = (S1687P.map (algebraMap ℚ K)).comp (X ^ 2) := by
  rw [show S1687H = S1687P.comp (X ^ 2) from S1687H_eq_comp, Polynomial.map_comp]
  simp

/-- S1687H splits in K. -/
theorem S1999H_splits : (S1687H.map (algebraMap ℚ S1993KP)).Splits := by
  have hP : (S1687P.map (algebraMap ℚ S1993KP)).Splits :=
    Polynomial.SplittingField.splits S1687P
  have hne : S1687P.map (algebraMap ℚ S1993KP) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ S1993KP).injective).mpr S1687P_ne_zero
  have hcomp : ((S1687P.map (algebraMap ℚ S1993KP)).comp (X ^ 2)).Splits := by
    refine S1999_splits_comp_X_sq hP ?_
    intro t ht
    refine S1999_root_isSquare t ?_
    have hroot : (S1687P.map (algebraMap ℚ S1993KP)).IsRoot t := (mem_roots hne).mp ht
    simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map] using hroot
  rw [S1999H_map_eq]
  exact hcomp

/-! ## 4. The root rho = B(alpha) * sqrt(-3) of S1687H -/

/-- The explicit square root of alpha in K. -/
noncomputable def S1999Rho : S1993KP := aeval S1993Alpha S1993B * S1993SqrtNegThree

theorem S1999Rho_sq : S1999Rho ^ 2 = S1993Alpha := by
  rw [S1999Rho, mul_pow, S1993B_sq S1993Alpha S1993Alpha_root, S1993SqrtNegThree_sq]
  have h : -(S1993Alpha / 3) * (-3 : S1993KP) = S1993Alpha := by
    field_simp
  exact h

theorem S1999Rho_root : aeval S1999Rho S1687H = 0 := by
  rw [show S1687H = S1687P.comp (X ^ 2) from S1687H_eq_comp, Polynomial.aeval_comp]
  have h2 : aeval S1999Rho (X ^ 2 : ℚ[X]) = S1999Rho ^ 2 := by simp
  rw [h2, S1999Rho_sq, S1993Alpha_root]

theorem S1999Rho_mem_rootSet : S1999Rho ∈ S1687H.rootSet S1993KP :=
  (Polynomial.mem_rootSet_of_ne S1687H_ne_zero).mpr S1999Rho_root

/-! ## 5. K is generated by the roots of S1687H -/

/-- Generation: the roots of S1687H generate K over Q. -/
theorem S1999_adjoin_eq_top :
    IntermediateField.adjoin ℚ (S1687H.rootSet S1993KP : Set S1993KP) = ⊤ := by
  set A : IntermediateField ℚ S1993KP :=
    IntermediateField.adjoin ℚ (S1687H.rootSet S1993KP : Set S1993KP) with hA
  have hρ : S1999Rho ∈ A := IntermediateField.subset_adjoin ℚ _ S1999Rho_mem_rootSet
  have hα : S1993Alpha ∈ A := by
    have h : S1999Rho * S1999Rho ∈ A := mul_mem hρ hρ
    have h2 : S1999Rho ^ 2 ∈ A := by rwa [pow_two]
    rwa [S1999Rho_sq] at h2
  have hB : aeval S1993Alpha S1993B ∈ A := by
    have hle : Algebra.adjoin ℚ ({S1993Alpha} : Set S1993KP) ≤ A.toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hα
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hle
    exact hle ⟨S1993B, rfl⟩
  have hBne : aeval S1993Alpha S1993B ≠ 0 := by
    intro h0
    have h := S1993B_sq S1993Alpha S1993Alpha_root
    rw [h0] at h
    have h1 : -(S1993Alpha / 3) = 0 := by rw [← h]; norm_num
    have h2 : S1993Alpha / 3 = 0 := neg_eq_zero.mp h1
    have h3 : S1993Alpha = 3 * (S1993Alpha / 3) := by field_simp
    rw [h2, mul_zero] at h3
    exact S1999Alpha_ne_zero h3
  have hs : S1993SqrtNegThree ∈ A := by
    have heq : S1993SqrtNegThree = S1999Rho * (aeval S1993Alpha S1993B)⁻¹ := by
      rw [S1999Rho]
      field_simp
    rw [heq]
    exact mul_mem hρ (inv_mem hB)
  rw [eq_top_iff, ← S1993_sup_eq_top]
  exact sup_le (IntermediateField.adjoin_simple_le_iff.mpr hα)
    (IntermediateField.adjoin_simple_le_iff.mpr hs)

/-- The Algebra.adjoin form of the generation statement. -/
theorem S1999_algAdjoin_eq_top :
    Algebra.adjoin ℚ (S1687H.rootSet S1993KP : Set S1993KP) = ⊤ := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (S :=
    (S1687H.rootSet S1993KP : Set S1993KP)) (fun x _ => IsAlgebraic.of_finite ℚ x),
    S1999_adjoin_eq_top]
  exact IntermediateField.top_toSubalgebra

/-! ## 6. The splitting field bridge -/

/-- K is a splitting field of S1687H. -/
theorem S1999_isSplittingFieldH : IsSplittingField ℚ S1993KP S1687H :=
  Polynomial.IsSplittingField.mk S1999H_splits S1999_algAdjoin_eq_top

/-- The first missing of S1993, proved: S1687Field is Q-isomorphic
to K = SplittingField S1687P. -/
theorem S1999SplittingFieldH_eq : Nonempty (S1687Field ≃ₐ[ℚ] S1993KP) := by
  letI : IsSplittingField ℚ S1993KP S1687H := S1999_isSplittingFieldH
  exact ⟨(Polynomial.IsSplittingField.algEquiv (K := ℚ) (L := S1993KP) S1687H).symm⟩


/-! ## 7. The next missing: sqrt(-1), and the uniqueness of the quadratic subfield -/

/-- 3 is not a square in Q. -/
theorem S1999_not_isSquare_three : ¬ IsSquare (3 : ℚ) := by
  have h : ¬ IsSquare ((3 : ℕ) : ℚ) := by
    rw [Rat.isSquare_natCast_iff]
    exact Nat.prime_three.not_isSquare
  simpa using h

/-- 3 is not a square of a rational number. -/
theorem S1999_sq_ne_three (q : ℚ) : q ^ 2 ≠ 3 := by
  intro h
  exact S1999_not_isSquare_three ⟨q, by rw [← pow_two]; exact h.symm⟩

/-- Every element of Q(sqrt(-3)) is of the form a + b * sqrt(-3). -/
theorem S1999_mem_adjoin_s (x : S1993KP) :
    x ∈ (ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP) ↔
      ∃ a b : ℚ, x = algebraMap ℚ S1993KP a + algebraMap ℚ S1993KP b * S1993SqrtNegThree := by
  have halg : IsAlgebraic ℚ S1993SqrtNegThree := (IsIntegral.of_finite ℚ _).isAlgebraic
  constructor
  · intro hx
    have hx' : x ∈ Algebra.adjoin ℚ ({S1993SqrtNegThree} : Set S1993KP) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := ℚ) (E := S1993KP)
        (α := S1993SqrtNegThree) halg]
      exact hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
    obtain ⟨p, hp⟩ := hx'
    have hp' : aeval S1993SqrtNegThree p = x := hp
    set f : ℚ[X] := X ^ 2 + C 3 with hf
    have hfmonic : f.Monic := monic_X_pow_add_C 3 (by norm_num)
    have hfdeg : f.degree = (2 : WithBot ℕ) := by rw [hf]; compute_degree!
    have hdeg : (p %ₘ f).natDegree ≤ 1 := by
      rcases eq_or_ne (p %ₘ f) 0 with h0 | h0
      · rw [h0]; simp
      · have hlt : (p %ₘ f).degree < (2 : WithBot ℕ) := by
          rw [← hfdeg]; exact degree_modByMonic_lt p hfmonic
        have hlt' : (p %ₘ f).degree < ((2 : ℕ) : WithBot ℕ) := by simpa using hlt
        have h2 : (p %ₘ f).natDegree < 2 :=
          (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hlt'
        omega
    have hf0 : aeval S1993SqrtNegThree f = 0 := by
      rw [hf]
      simp only [map_add, map_pow, aeval_X, aeval_C]
      rw [S1993SqrtNegThree_sq]
      norm_num
    have hmod : aeval S1993SqrtNegThree (p %ₘ f) = aeval S1993SqrtNegThree p := by
      conv_rhs => rw [← modByMonic_add_div p f]
      rw [map_add, map_mul, hf0, zero_mul, add_zero]
    refine ⟨(p %ₘ f).coeff 0, (p %ₘ f).coeff 1, ?_⟩
    rw [← hp', ← hmod]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg]
    simp only [map_add, map_mul, aeval_X, aeval_C]
    ring
  · rintro ⟨a, b, rfl⟩
    refine add_mem (IntermediateField.algebraMap_mem _ a)
      (mul_mem (IntermediateField.algebraMap_mem _ b) ?_)
    exact IntermediateField.mem_adjoin_simple_self ℚ S1993SqrtNegThree

/-- sqrt(-3) is not a rational number, i.e. it is not in the prime field. -/
theorem S1999_sqrtNegThree_notMem_bot :
    S1993SqrtNegThree ∉ (⊥ : IntermediateField ℚ S1993KP) := by
  rw [IntermediateField.mem_bot]
  rintro ⟨q, hq⟩
  have h : q ^ 2 = -3 := by
    apply (algebraMap ℚ S1993KP).injective
    rw [map_pow, map_neg, map_ofNat, hq]
    exact S1993SqrtNegThree_sq
  nlinarith [sq_nonneg q]

/-- **There is no square root of -1 inside Q(sqrt(-3))**.  This is the last
algebraic step of the argument that K contains no sqrt(-1): it uses only the
explicit normal form a + b * sqrt(-3) of elements of Q(sqrt(-3)). -/
theorem S1999_no_sqrt_neg_one_in_adjoin_s (x : S1993KP)
    (hxmem : x ∈ (ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP))
    (hx : x ^ 2 = -1) : False := by
  obtain ⟨a, b, hab⟩ := (S1999_mem_adjoin_s x).mp hxmem
  have hA : algebraMap ℚ S1993KP (a ^ 2 - 3 * b ^ 2)
      = (algebraMap ℚ S1993KP a) ^ 2 - 3 * (algebraMap ℚ S1993KP b) ^ 2 := by
    rw [map_sub, map_mul, map_pow, map_pow,
      show algebraMap ℚ S1993KP (3 : ℚ) = 3 by norm_num]
  have hB : algebraMap ℚ S1993KP (2 * a * b)
      = 2 * (algebraMap ℚ S1993KP a) * (algebraMap ℚ S1993KP b) := by
    rw [map_mul, map_mul, show algebraMap ℚ S1993KP (2 : ℚ) = 2 by norm_num]
  have h2 : (algebraMap ℚ S1993KP a + algebraMap ℚ S1993KP b * S1993SqrtNegThree) ^ 2
      = algebraMap ℚ S1993KP (a ^ 2 - 3 * b ^ 2)
        + algebraMap ℚ S1993KP (2 * a * b) * S1993SqrtNegThree := by
    rw [hA, hB]
    linear_combination (algebraMap ℚ S1993KP b) ^ 2 * S1993SqrtNegThree_sq
  have hkey : algebraMap ℚ S1993KP (a ^ 2 - 3 * b ^ 2 + 1)
      + algebraMap ℚ S1993KP (2 * a * b) * S1993SqrtNegThree = 0 := by
    have h1 : (algebraMap ℚ S1993KP a + algebraMap ℚ S1993KP b * S1993SqrtNegThree) ^ 2
        = -1 := by
      rw [← hab]; exact hx
    rw [h2] at h1
    have hcast : algebraMap ℚ S1993KP (a ^ 2 - 3 * b ^ 2 + 1)
        = algebraMap ℚ S1993KP (a ^ 2 - 3 * b ^ 2) + 1 := by
      rw [show a ^ 2 - 3 * b ^ 2 + 1 = (a ^ 2 - 3 * b ^ 2) + 1 by ring, map_add, map_one]
    rw [hcast]
    linear_combination h1
  have hab0 : a * b = 0 := by
    by_contra hne
    have hd : algebraMap ℚ S1993KP (2 * a * b) ≠ 0 := by
      intro h
      have h0 : (2 * a * b : ℚ) = 0 := (algebraMap ℚ S1993KP).injective (by simpa using h)
      exact hne (by linarith)
    have hmem : S1993SqrtNegThree ∈ (⊥ : IntermediateField ℚ S1993KP) := by
      rw [IntermediateField.mem_bot]
      refine ⟨-(a ^ 2 - 3 * b ^ 2 + 1) / (2 * a * b), ?_⟩
      have h1 : S1993SqrtNegThree * algebraMap ℚ S1993KP (2 * a * b)
          = -algebraMap ℚ S1993KP (a ^ 2 - 3 * b ^ 2 + 1) := by
        rw [mul_comm]
        linear_combination hkey
      rw [map_div₀, map_neg, div_eq_iff hd]
      exact h1.symm
    exact S1999_sqrtNegThree_notMem_bot hmem
  have hval : a ^ 2 - 3 * b ^ 2 = -1 := by
    have hd : algebraMap ℚ S1993KP (2 * a * b) = 0 := by
      rw [show (2 * a * b : ℚ) = 2 * (a * b) by ring, hab0, mul_zero, map_zero]
    have hc : algebraMap ℚ S1993KP (a ^ 2 - 3 * b ^ 2 + 1) = 0 := by
      have h := hkey
      rw [hd, zero_mul, add_zero] at h
      exact h
    have h0 : (a ^ 2 - 3 * b ^ 2 + 1 : ℚ) = 0 :=
      (algebraMap ℚ S1993KP).injective (by simpa using hc)
    linarith
  rcases mul_eq_zero.mp hab0 with ha | hb
  · have hb2 : b ^ 2 = 1 / 3 := by rw [ha] at hval; linarith
    have h3 : (3 * b) ^ 2 = 3 := by linear_combination 9 * hb2
    exact S1999_sq_ne_three (3 * b) h3
  · have ha2 : a ^ 2 = -1 := by rw [hb] at hval; linarith
    nlinarith [sq_nonneg a]

/-- The minimal polynomial of a square root of -1 is X^2 + 1, hence its degree is 2. -/
theorem S1999_minpoly_of_sq_eq_neg_one (x : S1993KP) (hx : x ^ 2 = -1) :
    minpoly ℚ x = X ^ 2 + C (1 : ℚ) := by
  have hirr : Irreducible (X ^ 2 + C (1 : ℚ) : ℚ[X]) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · have hdeg : (X ^ 2 + C (1 : ℚ) : ℚ[X]).natDegree = 2 :=
        Polynomial.natDegree_eq_of_degree_eq_some (by compute_degree!)
      rw [hdeg]; norm_num
    · intro q hq
      simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] at hq
      nlinarith [sq_nonneg q]
  have haev : aeval x (X ^ 2 + C (1 : ℚ) : ℚ[X]) = 0 := by
    simp only [map_add, map_pow, aeval_X, aeval_C]
    rw [hx]
    norm_num
  have hmonic : (X ^ 2 + C (1 : ℚ) : ℚ[X]).Monic := monic_X_pow_add_C 1 (by norm_num)
  exact (minpoly.eq_of_irreducible_of_monic hirr haev hmonic).symm

/-- **The exact next missing of the S1993 bridge**: K = SplittingField S1687P has no
square root of -1, i.e. K does not contain Q(i).  Equivalently, K and Q(i) are
linearly disjoint over Q. -/
def S1999KNoSqrtNegOne : Prop := ∀ x : S1993KP, x ^ 2 ≠ -1

/-- The quadratic subfield of K is unique: it is Q(sqrt(-3)). -/
def S1999QuadraticSubfieldUnique : Prop :=
  ∀ L : IntermediateField ℚ S1993KP, Module.finrank ℚ L = 2 → L = ℚ⟮S1993SqrtNegThree⟯

/-- **Reduction of the next missing**: uniqueness of the quadratic subfield of K
implies that K has no square root of -1.  (The converse direction, and hence the
uniqueness itself, is exactly what is not proved in this file: it requires the
exclusion of a degree-3 compositum Q(sqrt(-3)) ⊔ Q(x) inside the degree-6 field K.) -/
theorem S1999KNoSqrtNegOne_of_quadraticSubfieldUnique (h : S1999QuadraticSubfieldUnique) :
    S1999KNoSqrtNegOne := by
  intro x hx
  have hxint : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
  have hxfin : Module.finrank ℚ (ℚ⟮x⟯ : IntermediateField ℚ S1993KP) = 2 := by
    rw [IntermediateField.adjoin.finrank hxint, S1999_minpoly_of_sq_eq_neg_one x hx]
    exact Polynomial.natDegree_eq_of_degree_eq_some (by compute_degree!)
  have hEq := h ℚ⟮x⟯ hxfin
  exact S1999_no_sqrt_neg_one_in_adjoin_s x (by
    rw [← hEq]; exact IntermediateField.mem_adjoin_simple_self ℚ x) hx

/-! ## 8. Consequences of the bridge for S1687Field -/

/-- [S1687Field : Q] = 6. -/
theorem S1999S1687Field_finrank : Module.finrank ℚ S1687Field = 6 :=
  S1993S1687Field_finrank_of_splitting S1999SplittingFieldH_eq

/-- Gal(S1687H/Q) is the full symmetric group on the three roots of P. -/
theorem S1999Gal_S1687H :
    Nonempty (Polynomial.Gal S1687H ≃* Equiv.Perm (S1687P.rootSet S1993KP)) :=
  S1993Gal_S1687Field_of_splitting S1999SplittingFieldH_eq

/-- Gal(S1687H/Q) has 6 elements. -/
theorem S1999Gal_S1687H_card : Nat.card (Polynomial.Gal S1687H) = 6 := by
  obtain ⟨e⟩ := S1999Gal_S1687H
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, S1993P_card_rootSet]
  norm_num

#print axioms S1999SplittingFieldH_eq
#print axioms S1999S1687Field_finrank
#print axioms S1999Gal_S1687H
#print axioms S1999Gal_S1687H_card
#print axioms S1999_no_sqrt_neg_one_in_adjoin_s
#print axioms S1999KNoSqrtNegOne_of_quadraticSubfieldUnique

end LeanFormal.IUT.XiFPaper.S1999S1993BridgeActual

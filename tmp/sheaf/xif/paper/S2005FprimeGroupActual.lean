/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import tmp.sheaf.xif.paper.S2003KNoSqrtNegOneActual
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Separable

/-!
# S2005: the Galois group and the quadratic subfields of F' = SplittingField (S1687H * (X^2+1))

This file closes the F'-block of S1993.  Let

* P = S1687P and K = S1993KP = SplittingField P, so that Gal(K/Q) = S_3 and
  [K : Q] = 6 (S1993, S1999),
* H = S1687H = P(X^2) and E = S1720Lift.fieldRange, the image inside F' of the
  splitting field of H, i.e. of the copy of K (S1999: S1687Field = SplittingField H
  is Q-isomorphic to K),
* F' = S1720Field = SplittingField (H * (X^2+1)) = SplittingField S1720H.

The three targets of S1993 are proved here:

* S2005_finrank              : [F' : Q] = 12,
* S2005FprimeGroupStructure  : Gal(F'/Q) = Gal(S1687H/Q) x Gal(X^2+1) = S_3 x C_2,
                               i.e. the Prop S1993FprimeGroupStructure,
* S2005QuadraticSubfields    : the Prop S1993QuadraticSubfields, i.e. F' contains
                               square roots of -3, 3 and -1, and every quadratic
                               subfield of F' is Q(sqrt(-3)), Q(sqrt(3)) or Q(i).

## The argument

1. E is the image of the splitting field of H under S1720Lift, hence [E : Q] = 6
   by transport of S1999S1687Field_finrank (S2005E_finrank).
2. Every root of H in F' lies in E: the canonical map on root sets
   Polynomial.Gal.mapRoots is bijective (S2005_roots_H_mem_E).  In particular the
   root r(c) of H attached by S1722 to a root c of P lies in E
   (S2005_r_mem_rootSet).
3. S1722 decomposes every root of S1720H as +-r(c) or +-i.  Since the root set of
   S1720H generates F' (SplittingField.adjoin_rootSet), F' is generated over Q by
   E and i (S2005E_sup_adjoin_I_eq_top), equivalently over the copy of K by i
   (S2005_adjoin_E_I_eq_top).
4. E contains no square root of -1 (S2005_no_sqrt_neg_one_in_E): such an element
   would transport along S2005Eq : S1687Field = K to a square root of -1 in K,
   contradicting S2003KNoSqrtNegOne.
5. Hence X^2+1 is irreducible over E, minpoly of i over E is X^2+1, and
   [F' : E] = 2 (S2005_finrank_over_E).  Together with [E : Q] = 6 the tower law
   gives [F' : Q] = 12 (S2005_finrank).
6. Since F'/Q is finite Galois, |Gal(F'/Q)| = 12 (S2005_gal_card).  The restriction
   map Polynomial.Gal.restrictProd S1687H S1720SqrtPolynomial is injective for any
   two polynomials, and the two sides have the same cardinality
   6 * 2 = 12 (S1999Gal_S1687H_card, S2005_gal_sqrt_card), so it is a mul equiv:
   Gal(F'/Q) = Gal(S1687H/Q) x Gal(X^2+1) (S2005FprimeGroupStructure).
7. For the quadratic subfields, write any x in F' as a + b*i with a, b in E
   (S2005_normal_form, from the degree-2 normal form over E).  If x^2 is rational
   then either x is in E or x is i times an element of E
   (S2005_eq_or_mul_I_of_sq_mem).
   * inside E the only quadratic subfield is Q(sqrt(-3)) (S2005_quadratic_unique,
     a degree count: two distinct quadratic subfields generate a degree-4 field,
     which cannot sit inside the degree-6 field E), and every element of
     Q(sqrt(-3)) is a + b sqrt(-3) (S2005_mem_adjoin_S); a rational square y^2 in
     E is therefore -3 r^2 (S2005_sq_form_of_mem_E);
   * i times a rational number has square -1 b^2; i times a non-rational element
     b of E with b^2 rational has square 3 r^2, again by the classification inside E.
   This yields S1993QuadraticSubfields (S2005QuadraticSubfields).

## Verification status

The file compiles (EXIT 0) with no sorry, admit, axiom, opaque declaration or
native_decide.  The axiom footprint of each main theorem is propext,
Classical.choice and Quot.sound only; see the #print axioms block at the end.

## Consumers

* S1993D5FiniteGroupBridgeActual: the F'-block of (6) is now closed.
* S1720SourceArithmeticActual / S1722DegreePrimeActual: [F' : Q] = 12 is the exact
  degree of the field F' on which the paper's arithmetic input lives.
-/


noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2005FprimeGroupActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1722DegreePrimeActual
open LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual
open LeanFormal.IUT.XiFPaper.S1999S1993BridgeActual
open LeanFormal.IUT.XiFPaper.S2003KNoSqrtNegOneActual
open scoped IntermediateField

attribute [local instance] Classical.decEq

/-! ## 1. The copy of K inside F', and the two quadratic elements -/

/-- The image of the splitting field of S1687H inside F', i.e. the copy of
K = SplittingField S1687P transported along the S1999 bridge. -/
abbrev S2005E : IntermediateField ℚ S1720Field := S1720Lift.fieldRange

/-- A square root of -1 in F' (the S1722 choice). -/
abbrev S2005I : S1720Field := iroot

/-- A chosen Q-algebra equivalence S1687Field -> K (the S1999 bridge). -/
noncomputable def S2005Eq : S1687Field ≃ₐ[ℚ] S1993KP := Classical.choice S1999SplittingFieldH_eq

/-- A square root of -3 in F', obtained as the image of the explicit
S1993SqrtNegThree in K. -/
noncomputable def S2005S : S1720Field := S1720Lift (S2005Eq.symm S1993SqrtNegThree)

theorem S2005Lift_injective : Function.Injective S1720Lift := by
  intro x y h
  have h2 : (AlgHom.equivFieldRange S1720Lift) x = (AlgHom.equivFieldRange S1720Lift) y := by
    apply Subtype.ext
    simpa using h
  exact (AlgHom.equivFieldRange S1720Lift).injective h2

theorem S2005S_sq : S2005S ^ 2 = (-3 : S1720Field) := by
  have h1 : (S2005Eq.symm S1993SqrtNegThree) ^ 2 = (-3 : S1687Field) := by
    rw [← map_pow, S1993SqrtNegThree_sq]
    rw [show (-3 : S1993KP) = algebraMap ℚ S1993KP (-3) by norm_num, AlgEquiv.commutes]
    norm_num
  rw [S2005S, ← map_pow, h1]
  rw [show (-3 : S1687Field) = algebraMap ℚ S1687Field (-3) by norm_num, AlgHom.commutes]
  norm_num

theorem S2005I_sq : S2005I ^ 2 = (-1 : S1720Field) := iroot_sq

theorem S2005S_notMem_bot : S2005S ∉ (⊥ : IntermediateField ℚ S1720Field) := by
  rw [IntermediateField.mem_bot]
  rintro ⟨q, hq⟩
  have hq2 : (q : ℚ) ^ 2 = -3 := by
    apply (algebraMap ℚ S1720Field).injective
    show algebraMap ℚ S1720Field (q ^ 2) = algebraMap ℚ S1720Field (-3)
    rw [map_pow, hq, S2005S_sq]
    norm_num
  nlinarith [sq_nonneg q]

theorem S2005I_notMem_bot : S2005I ∉ (⊥ : IntermediateField ℚ S1720Field) := by
  rw [IntermediateField.mem_bot]
  rintro ⟨q, hq⟩
  have hq2 : (q : ℚ) ^ 2 = -1 := by
    apply (algebraMap ℚ S1720Field).injective
    show algebraMap ℚ S1720Field (q ^ 2) = algebraMap ℚ S1720Field (-1)
    rw [map_pow, hq, S2005I_sq]
    norm_num
  nlinarith [sq_nonneg q]

/-- Minimal polynomial of a non-rational square root of a rational number. -/
theorem S2005_minpoly_sq {L : Type*} [Field L] [Algebra ℚ L] [CharZero L]
    {x : L} {q : ℚ} (hx : x ^ 2 = algebraMap ℚ L q)
    (hxbot : x ∉ (⊥ : IntermediateField ℚ L)) :
    minpoly ℚ x = X ^ 2 - C q := by
  have hmonic : (X ^ 2 - C q : ℚ[X]).Monic := monic_X_pow_sub_C q (by norm_num : (2 : ℕ) ≠ 0)
  have hdeg : (X ^ 2 - C q : ℚ[X]).natDegree = 2 := natDegree_X_pow_sub_C
  have hirr : Irreducible (X ^ 2 - C q : ℚ[X]) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [hdeg]; norm_num
    · intro r hr
      have hr' : r ^ 2 = q := by
        have h0 : r ^ 2 - q = 0 := by
          simpa [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C] using hr
        exact sub_eq_zero.mp h0
      apply hxbot
      rw [IntermediateField.mem_bot]
      have hsq : x ^ 2 = (algebraMap ℚ L r) ^ 2 := by rw [hx, ← map_pow, hr']
      rcases eq_or_eq_neg_of_sq_eq_sq x (algebraMap ℚ L r) hsq with h | h
      · exact ⟨r, h.symm⟩
      · exact ⟨-r, by rw [h, map_neg]⟩
  have haev : aeval x (X ^ 2 - C q : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [hx, sub_self]
  exact (minpoly.eq_of_irreducible_of_monic hirr haev hmonic).symm

/-- A non-rational square root of a rational number generates a quadratic field. -/
theorem S2005_finrank_adjoin_sq {L : Type*} [Field L] [Algebra ℚ L] [CharZero L]
    {x : L} {q : ℚ} (hx : x ^ 2 = algebraMap ℚ L q)
    (hxbot : x ∉ (⊥ : IntermediateField ℚ L)) :
    Module.finrank ℚ (ℚ⟮x⟯ : IntermediateField ℚ L) = 2 := by
  have haev : aeval x (X ^ 2 - C q : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [hx, sub_self]
  have hint : IsIntegral ℚ x :=
    ⟨X ^ 2 - C q, monic_X_pow_sub_C q (by norm_num : (2 : ℕ) ≠ 0),
      by simpa [Polynomial.aeval_def] using haev⟩
  rw [IntermediateField.adjoin.finrank hint, S2005_minpoly_sq hx hxbot, natDegree_X_pow_sub_C]

theorem S2005S_adjoin_finrank :
    Module.finrank ℚ (ℚ⟮S2005S⟯ : IntermediateField ℚ S1720Field) = 2 := by
  refine S2005_finrank_adjoin_sq (q := -3) ?_ S2005S_notMem_bot
  rw [S2005S_sq]
  norm_num

theorem S2005I_adjoin_finrank :
    Module.finrank ℚ (ℚ⟮S2005I⟯ : IntermediateField ℚ S1720Field) = 2 := by
  refine S2005_finrank_adjoin_sq (q := -1) ?_ S2005I_notMem_bot
  rw [S2005I_sq]
  norm_num

/-! ## 2. The normal form in Q(sqrt(-3)) inside F' -/

/-- Every element of Q(sqrt(-3)) inside F' is a + b * sqrt(-3). -/
theorem S2005_mem_adjoin_S (x : S1720Field) :
    x ∈ (ℚ⟮S2005S⟯ : IntermediateField ℚ S1720Field) ↔
      ∃ a b : ℚ, x = algebraMap ℚ S1720Field a + algebraMap ℚ S1720Field b * S2005S := by
  have haev3 : aeval S2005S (X ^ 2 - C (-3) : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [S2005S_sq]
    norm_num
  have hint : IsIntegral ℚ S2005S :=
    ⟨X ^ 2 - C (-3), monic_X_pow_sub_C (-3) (by norm_num : (2 : ℕ) ≠ 0),
      by simpa [Polynomial.aeval_def] using haev3⟩
  have halg : IsAlgebraic ℚ S2005S := hint.isAlgebraic
  constructor
  · intro hx
    have hx' : x ∈ Algebra.adjoin ℚ ({S2005S} : Set S1720Field) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := ℚ) (E := S1720Field)
        (α := S2005S) halg]
      exact hx
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
    obtain ⟨p, hp⟩ := hx'
    have hp' : aeval S2005S p = x := hp
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
    have hf0 : aeval S2005S f = 0 := by
      rw [hf]
      simp only [map_add, map_pow, aeval_X, aeval_C]
      rw [S2005S_sq]
      norm_num
    have hmod : aeval S2005S (p %ₘ f) = aeval S2005S p := by
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
    exact IntermediateField.mem_adjoin_simple_self ℚ S2005S

/-- A rational relation u + v * sqrt(-3) = 0 has u = v = 0. -/
theorem S2005_eq_zero_of_add_mul_S {u v : ℚ}
    (h : algebraMap ℚ S1720Field u + algebraMap ℚ S1720Field v * S2005S = 0) :
    u = 0 ∧ v = 0 := by
  by_cases hv : v = 0
  · subst hv
    have h0 : algebraMap ℚ S1720Field u = 0 := by simpa using h
    exact ⟨(algebraMap ℚ S1720Field).injective (by simpa using h0), rfl⟩
  · exfalso
    have hv' : algebraMap ℚ S1720Field v ≠ 0 := by
      intro h0
      exact hv ((algebraMap ℚ S1720Field).injective (by simpa using h0))
    have h1 : S2005S * algebraMap ℚ S1720Field v = -algebraMap ℚ S1720Field u := by
      rw [mul_comm]
      linear_combination h
    have hs : S2005S = algebraMap ℚ S1720Field ((-u) / v) := by
      rw [map_div₀, map_neg]
      rw [eq_div_iff hv']
      linear_combination h1
    exact S2005S_notMem_bot (by
      rw [IntermediateField.mem_bot]
      exact ⟨(-u) / v, hs.symm⟩)


/-! ## 3. The copy of K inside F' has degree 6, and contains no square root of -1 -/

theorem S2005E_finrank : Module.finrank ℚ S2005E = 6 := by
  have h : Module.finrank ℚ S1687Field = Module.finrank ℚ S1720Lift.fieldRange :=
    (AlgHom.equivFieldRange S1720Lift).toLinearEquiv.finrank_eq
  rw [← h]
  exact S1999S1687Field_finrank

/-- Every root of S1687H in F' lies in the chosen copy of K. -/
theorem S2005_roots_H_mem_E {x : S1720Field} (hx : x ∈ S1687H.rootSet S1720Field) :
    x ∈ S2005E := by
  haveI : Fact ((S1687H.map (algebraMap ℚ S1720Field)).Splits) := ⟨S1687H_splits_in_F'⟩
  obtain ⟨y, hy⟩ :=
    (Polynomial.Gal.mapRoots_bijective (p := S1687H) (E := S1720Field)).2 ⟨x, hx⟩
  refine ⟨(y : S1687Field), ?_⟩
  have h1 : ((Polynomial.Gal.mapRoots S1687H S1720Field y : S1687H.rootSet S1720Field) :
      S1720Field) = x := congrArg Subtype.val hy
  have h2 : ((Polynomial.Gal.mapRoots S1687H S1720Field y : S1687H.rootSet S1720Field) :
      S1720Field) = S1720Lift (y : S1687Field) := rfl
  rw [h2] at h1
  exact h1

/-- The copy of K inside F' contains no square root of -1. -/
theorem S2005_no_sqrt_neg_one_in_E {x : S1720Field} (hxE : x ∈ S2005E)
    (hx : x ^ 2 = (-1 : S1720Field)) : False := by
  obtain ⟨y, rfl⟩ := hxE
  have hy : y ^ 2 = (-1 : S1687Field) := by
    apply S2005Lift_injective
    have hx' : S1720Lift y ^ 2 = (-1 : S1720Field) := hx
    rw [map_pow, hx']
    simp
  have h2 : (S2005Eq y) ^ 2 = (-1 : S1993KP) := by
    rw [← map_pow, hy]
    simp
  exact S2003KNoSqrtNegOne (S2005Eq y) h2

theorem S2005I_notMem_E : S2005I ∉ S2005E :=
  fun h => S2005_no_sqrt_neg_one_in_E h S2005I_sq

/-! ## 4. F' is generated over the copy of K by i = sqrt(-1) -/

theorem S2005_adjoin_rootSet_eq_top :
    IntermediateField.adjoin ℚ (S1720H.rootSet S1720Field : Set S1720Field) = ⊤ := by
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.top_toSubalgebra]
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => IsAlgebraic.of_finite ℚ x)]
  exact Polynomial.SplittingField.adjoin_rootSet (f := S1720H)

/-- The square root of a root of S1687P is a root of S1687H. -/
theorem S2005_r_mem_rootSet (c : S1687P.rootSet S1720Field) :
    S1722DegreePrimeActual.r c ∈ S1687H.rootSet S1720Field := by
  rw [Polynomial.mem_rootSet_of_ne S1687H_ne_zero]
  rw [S1687H_eq_comp, Polynomial.aeval_comp]
  have h2 : aeval (S1722DegreePrimeActual.r c) (X ^ 2 : ℚ[X]) =
      (S1722DegreePrimeActual.r c) ^ 2 := by simp
  rw [h2, S1722DegreePrimeActual.r_sq]
  exact (Polynomial.mem_rootSet_of_ne S1687P_ne_zero).mp c.2

theorem S2005E_sup_adjoin_I_eq_top :
    S2005E ⊔ (ℚ⟮S2005I⟯ : IntermediateField ℚ S1720Field) = ⊤ := by
  have hroot : ∀ x ∈ (S1720H.rootSet S1720Field : Set S1720Field),
      x ∈ S2005E ⊔ (ℚ⟮S2005I⟯ : IntermediateField ℚ S1720Field) := by
    intro x hx
    rcases S1722DegreePrimeActual.root_decomp hx with ⟨c, h | h⟩ | h | h
    · rw [h]
      exact SetLike.le_def.mp le_sup_left (S2005_roots_H_mem_E (S2005_r_mem_rootSet c))
    · rw [h]
      exact neg_mem (SetLike.le_def.mp le_sup_left (S2005_roots_H_mem_E (S2005_r_mem_rootSet c)))
    · rw [h]
      exact SetLike.le_def.mp le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ S2005I)
    · rw [h]
      exact neg_mem (SetLike.le_def.mp le_sup_right
        (IntermediateField.mem_adjoin_simple_self ℚ S2005I))
  have hle : (IntermediateField.adjoin ℚ (S1720H.rootSet S1720Field : Set S1720Field)) ≤
      S2005E ⊔ (ℚ⟮S2005I⟯ : IntermediateField ℚ S1720Field) := by
    rw [IntermediateField.adjoin_le_iff]
    exact hroot
  rw [S2005_adjoin_rootSet_eq_top] at hle
  exact le_antisymm le_top hle

/-- The same generation statement with F' viewed as an extension of the copy of K. -/
theorem S2005_adjoin_E_I_eq_top :
    IntermediateField.adjoin (↥S2005E) ({S2005I} : Set S1720Field) = ⊤ := by
  have h := IntermediateField.restrictScalars_adjoin_eq_sup (F := ℚ) (E := S1720Field)
    S2005E ({S2005I} : Set S1720Field)
  rw [S2005E_sup_adjoin_I_eq_top] at h
  exact (IntermediateField.restrictScalars_eq_top_iff).mp h

theorem S2005I_minpoly_over_E :
    minpoly (↥S2005E) S2005I = X ^ 2 + C (1 : ↥S2005E) := by
  have hmonic : (X ^ 2 + C (1 : ↥S2005E)).Monic := monic_X_pow_add_C 1 (by norm_num)
  have haev : aeval S2005I (X ^ 2 + C (1 : ↥S2005E)) = 0 := by
    simp only [map_add, map_pow, aeval_X, aeval_C]
    rw [S2005I_sq, map_one]
    norm_num
  have hirr : Irreducible (X ^ 2 + C (1 : ↥S2005E)) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · have hdeg : (X ^ 2 + C (1 : ↥S2005E)).natDegree = 2 := natDegree_X_pow_add_C
      rw [hdeg]; norm_num
    · intro y hy
      have hy0 : y ^ 2 + 1 = 0 := by
        simpa [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C] using hy
      have hy1 : y ^ 2 = (-1 : ↥S2005E) := by linear_combination hy0
      have hy2 : (y : S1720Field) ^ 2 = (-1 : S1720Field) := by
        have h := congrArg (fun z : ↥S2005E => (z : S1720Field)) hy1
        simpa using h
      exact S2005_no_sqrt_neg_one_in_E y.2 hy2
  exact (minpoly.eq_of_irreducible_of_monic hirr haev hmonic).symm

theorem S2005_finrank_over_E : Module.finrank (↥S2005E) S1720Field = 2 := by
  have haev : aeval S2005I (X ^ 2 + C (1 : ↥S2005E)) = 0 := by
    simp only [map_add, map_pow, aeval_X, aeval_C]
    rw [S2005I_sq, map_one]
    norm_num
  have hint : IsIntegral (↥S2005E) S2005I :=
    ⟨X ^ 2 + C (1 : ↥S2005E), monic_X_pow_add_C 1 (by norm_num),
      by simpa [Polynomial.aeval_def] using haev⟩
  rw [← IntermediateField.finrank_top' (F := ↥S2005E) (E := S1720Field),
    ← S2005_adjoin_E_I_eq_top, IntermediateField.adjoin.finrank hint,
    S2005I_minpoly_over_E]
  exact natDegree_X_pow_add_C

/-- **[F' : Q] = 12**. -/
theorem S2005_finrank : Module.finrank ℚ S1720Field = 12 := by
  have h := Module.finrank_mul_finrank ℚ (↥S2005E) S1720Field
  rw [S2005E_finrank, S2005_finrank_over_E] at h
  omega

/-! ## 5. The Galois group of F' is the product of the Galois groups of the two factors -/

theorem S2005_sqrtpoly_eq : S1720SqrtPolynomial = X ^ 2 - C (-1 : ℚ) := by
  rw [S1720SqrtPolynomial]
  have h : (C (-1 : ℚ) : ℚ[X]) = -1 := by simp
  rw [h]
  ring

theorem S2005_sqrtpoly_natDegree : S1720SqrtPolynomial.natDegree = 2 := by
  rw [S2005_sqrtpoly_eq]
  exact natDegree_X_pow_sub_C

theorem S2005_sqrtpoly_separable : S1720SqrtPolynomial.Separable := by
  rw [S2005_sqrtpoly_eq]
  exact separable_X_pow_sub_C (-1) (by norm_num : ((2 : ℕ) : ℚ) ≠ 0) (by norm_num)

theorem S2005_sqrtpoly_irreducible : Irreducible (S1720SqrtPolynomial : ℚ[X]) := by
  rw [S2005_sqrtpoly_eq]
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have hdeg : (X ^ 2 - C (-1 : ℚ) : ℚ[X]).natDegree = 2 := natDegree_X_pow_sub_C
    rw [hdeg]; norm_num
  · intro r hr
    have hr' : r ^ 2 = -1 := by
      have h0 : r ^ 2 - (-1) = 0 := by
        simpa [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C] using hr
      linarith
    nlinarith [sq_nonneg r]

/-- The Galois group of the S1687 sextic on F' has 12 elements, i.e. [F' : Q]. -/
theorem S2005_gal_card : Nat.card (Polynomial.Gal S1720H) = 12 := by
  have h : Nat.card (Polynomial.Gal S1720H) = Module.finrank ℚ S1720Field :=
    IsGalois.card_aut_eq_finrank ℚ S1720Field
  rw [h, S2005_finrank]

/-- The Galois group of X^2+1 has 2 elements. -/
theorem S2005_gal_sqrt_card : Nat.card (Polynomial.Gal S1720SqrtPolynomial) = 2 := by
  rw [Nat.card_eq_fintype_card]
  haveI : Fact ((S1720SqrtPolynomial.map
      (algebraMap ℚ (Polynomial.SplittingField S1720SqrtPolynomial))).Splits) :=
    ⟨Polynomial.SplittingField.splits S1720SqrtPolynomial⟩
  have hroot : Fintype.card (S1720SqrtPolynomial.rootSet
      (Polynomial.SplittingField S1720SqrtPolynomial)) = 2 := by
    have h := Polynomial.card_rootSet_eq_natDegree
      (K := Polynomial.SplittingField S1720SqrtPolynomial)
      S2005_sqrtpoly_separable (Polynomial.SplittingField.splits S1720SqrtPolynomial)
    rw [S2005_sqrtpoly_natDegree] at h
    exact h
  have hle : Fintype.card (Polynomial.Gal S1720SqrtPolynomial) ≤ 2 := by
    have hinj : Function.Injective (Polynomial.Gal.galActionHom S1720SqrtPolynomial
        (Polynomial.SplittingField S1720SqrtPolynomial)) :=
      Polynomial.Gal.galActionHom_injective S1720SqrtPolynomial
        (Polynomial.SplittingField S1720SqrtPolynomial)
    have h1 := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_perm, hroot] at h1
    simpa using h1
  have hge : 2 ≤ Fintype.card (Polynomial.Gal S1720SqrtPolynomial) := by
    obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card
      (show 1 < Fintype.card (S1720SqrtPolynomial.rootSet
        (Polynomial.SplittingField S1720SqrtPolynomial)) by rw [hroot]; norm_num)
    haveI : Fact (Irreducible S1720SqrtPolynomial) := ⟨S2005_sqrtpoly_irreducible⟩
    have htrans := Polynomial.Gal.galAction_isPretransitive (p := S1720SqrtPolynomial)
      (E := Polynomial.SplittingField S1720SqrtPolynomial) (Fact.out)
    obtain ⟨g, hg⟩ := htrans.exists_smul_eq x y
    have hg1 : g ≠ 1 := by
      intro h
      rw [h, one_smul] at hg
      exact hxy hg
    have h2 : 1 < Fintype.card (Polynomial.Gal S1720SqrtPolynomial) := by
      rw [Fintype.one_lt_card_iff_nontrivial]
      exact ⟨1, g, hg1.symm⟩
    omega
  omega

/-- The group structure of (6): the Galois group of F' = SplittingField (S1687H * (X^2+1))
is the direct product of the Galois groups of the two factors (S_3 x C_2). -/
theorem S2005FprimeGroupStructure : S1993FprimeGroupStructure := by
  refine ⟨?_⟩
  have hinj : Function.Injective
      (Polynomial.Gal.restrictProd S1687H S1720SqrtPolynomial) :=
    Polynomial.Gal.restrictProd_injective S1687H S1720SqrtPolynomial
  have hcard : Fintype.card (Polynomial.Gal S1720H) =
      Fintype.card (Polynomial.Gal S1687H × Polynomial.Gal S1720SqrtPolynomial) := by
    have h1 : Fintype.card (Polynomial.Gal S1720H) = 12 := by
      rw [← Nat.card_eq_fintype_card]; exact S2005_gal_card
    have h2 : Fintype.card (Polynomial.Gal S1687H) = 6 := by
      rw [← Nat.card_eq_fintype_card]; exact S1999Gal_S1687H_card
    have h3 : Fintype.card (Polynomial.Gal S1720SqrtPolynomial) = 2 := by
      rw [← Nat.card_eq_fintype_card]; exact S2005_gal_sqrt_card
    rw [h1, Fintype.card_prod, h2, h3]
  have hbij : Function.Bijective
      (Polynomial.Gal.restrictProd S1687H S1720SqrtPolynomial) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩
  exact MulEquiv.ofBijective _ hbij


/-! ## 6. The quadratic subfields of F' -/

theorem S2005S_mem_E : S2005S ∈ S2005E := by
  rw [S2005S]
  exact AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩

/-- The compositum of two distinct quadratic subfields of F' has degree 4. -/
theorem S2005_finrank_sup_of_ne {L M : IntermediateField ℚ S1720Field}
    (hL : Module.finrank ℚ L = 2) (hM : Module.finrank ℚ M = 2) (hne : L ≠ M) :
    Module.finrank ℚ ↥(L ⊔ M) = 4 := by
  have hle : Module.finrank ℚ ↥(L ⊔ M) ≤ 4 := by
    have h := IntermediateField.finrank_sup_le (K := ℚ) L M
    rw [hL, hM] at h
    simpa using h
  have hdvd : 2 ∣ Module.finrank ℚ ↥(L ⊔ M) := by
    have h := IntermediateField.finrank_dvd_of_le_right (F := L) (E := L ⊔ M) le_sup_left
    rwa [hL] at h
  have hne2 : Module.finrank ℚ ↥(L ⊔ M) ≠ 2 := by
    intro h2
    have hLM : L = L ⊔ M := by
      refine IntermediateField.eq_of_le_of_finrank_eq le_sup_left ?_
      rw [h2, hL]
    have hML : M ≤ L := by rw [hLM]; exact le_sup_right
    have hML' : M = L := IntermediateField.eq_of_le_of_finrank_eq hML (by rw [hM, hL])
    exact hne hML'.symm
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Module.finrank ℚ ↥(L ⊔ M) := Module.finrank_pos
  omega

/-- Every quadratic subfield of the copy of K inside F' is Q(sqrt(-3)). -/
theorem S2005_quadratic_unique {L : IntermediateField ℚ S1720Field} (hL : L ≤ S2005E)
    (hfin : Module.finrank ℚ L = 2) : L = ℚ⟮S2005S⟯ := by
  by_contra hne
  have hSle : (ℚ⟮S2005S⟯ : IntermediateField ℚ S1720Field) ≤ S2005E := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ S2005S_mem_E
  have h4 : Module.finrank ℚ ↥(L ⊔ ℚ⟮S2005S⟯) = 4 :=
    S2005_finrank_sup_of_ne hfin S2005S_adjoin_finrank hne
  have hle : (L ⊔ ℚ⟮S2005S⟯ : IntermediateField ℚ S1720Field) ≤ S2005E := sup_le hL hSle
  have hdvd : 4 ∣ Module.finrank ℚ S2005E := by
    rw [← h4]
    exact IntermediateField.finrank_dvd_of_le_right hle
  rw [S2005E_finrank] at hdvd
  norm_num at hdvd

/-- Normal form over the copy of K: every element of F' is a + b * i with a, b in K. -/
theorem S2005_normal_form (x : S1720Field) :
    ∃ a : S1720Field, a ∈ S2005E ∧ ∃ b : S1720Field, b ∈ S2005E ∧ x = a + b * S2005I := by
  have haev : aeval S2005I (X ^ 2 + C (1 : ↥S2005E)) = 0 := by
    simp only [map_add, map_pow, aeval_X, aeval_C]
    rw [S2005I_sq, map_one]
    norm_num
  have hint : IsIntegral (↥S2005E) S2005I :=
    ⟨X ^ 2 + C (1 : ↥S2005E), monic_X_pow_add_C 1 (by norm_num),
      by simpa [Polynomial.aeval_def] using haev⟩
  have halg : IsAlgebraic (↥S2005E) S2005I := hint.isAlgebraic
  have hx : x ∈ (IntermediateField.adjoin (↥S2005E) ({S2005I} : Set S1720Field) :
      IntermediateField (↥S2005E) S1720Field) := by
    rw [S2005_adjoin_E_I_eq_top]
    exact trivial
  have hx' : x ∈ Algebra.adjoin (↥S2005E) ({S2005I} : Set S1720Field) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := ↥S2005E)
      (E := S1720Field) (α := S2005I) halg]
    exact hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨p, hp⟩ := hx'
  have hp' : aeval S2005I p = x := hp
  set f : (↥S2005E)[X] := X ^ 2 + C 1 with hf
  have hfmonic : f.Monic := monic_X_pow_add_C 1 (by norm_num)
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
  have hf0 : aeval S2005I f = 0 := by
    rw [hf]
    simp only [map_add, map_pow, aeval_X, aeval_C]
    rw [S2005I_sq, map_one]
    norm_num
  have hmod : aeval S2005I (p %ₘ f) = aeval S2005I p := by
    conv_rhs => rw [← modByMonic_add_div p f]
    rw [map_add, map_mul, hf0, zero_mul, add_zero]
  refine ⟨algebraMap (↥S2005E) S1720Field ((p %ₘ f).coeff 0), ?_,
    algebraMap (↥S2005E) S1720Field ((p %ₘ f).coeff 1), ?_, ?_⟩
  · simpa using ((p %ₘ f).coeff 0).2
  · simpa using ((p %ₘ f).coeff 1).2
  · rw [← hp', ← hmod]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg]
    simp only [map_add, map_mul, aeval_X, aeval_C]
    ring

/-- A rational square in the copy of K is minus three times a rational square. -/
theorem S2005_sq_form_of_mem_E {y : S1720Field} (hy : y ∈ S2005E) (q : ℚ)
    (hyq : y ^ 2 = algebraMap ℚ S1720Field q)
    (hybot : y ∉ (⊥ : IntermediateField ℚ S1720Field)) :
    ∃ r : ℚ, y ^ 2 = algebraMap ℚ S1720Field (-3 * r ^ 2) := by
  have hfin : Module.finrank ℚ (ℚ⟮y⟯ : IntermediateField ℚ S1720Field) = 2 :=
    S2005_finrank_adjoin_sq hyq hybot
  have hyle : (ℚ⟮y⟯ : IntermediateField ℚ S1720Field) ≤ S2005E := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hy
  have heq := S2005_quadratic_unique hyle hfin
  have hymem : y ∈ (ℚ⟮S2005S⟯ : IntermediateField ℚ S1720Field) := by
    rw [← heq]
    exact IntermediateField.mem_adjoin_simple_self ℚ y
  obtain ⟨a, b, hab⟩ := (S2005_mem_adjoin_S y).mp hymem
  have hA : algebraMap ℚ S1720Field (a ^ 2 - 3 * b ^ 2)
      = (algebraMap ℚ S1720Field a) ^ 2 - 3 * (algebraMap ℚ S1720Field b) ^ 2 := by
    rw [map_sub, map_mul, map_pow, map_pow,
      show algebraMap ℚ S1720Field (3 : ℚ) = 3 by norm_num]
  have hB : algebraMap ℚ S1720Field (2 * a * b)
      = 2 * (algebraMap ℚ S1720Field a) * (algebraMap ℚ S1720Field b) := by
    rw [map_mul, map_mul, show algebraMap ℚ S1720Field (2 : ℚ) = 2 by norm_num]
  have hsq : (algebraMap ℚ S1720Field a + algebraMap ℚ S1720Field b * S2005S) ^ 2
      = algebraMap ℚ S1720Field (a ^ 2 - 3 * b ^ 2)
        + algebraMap ℚ S1720Field (2 * a * b) * S2005S := by
    rw [hA, hB]
    linear_combination (algebraMap ℚ S1720Field b) ^ 2 * S2005S_sq
  have hkey : algebraMap ℚ S1720Field (a ^ 2 - 3 * b ^ 2 - q)
      + algebraMap ℚ S1720Field (2 * a * b) * S2005S = 0 := by
    have h1 : (algebraMap ℚ S1720Field a + algebraMap ℚ S1720Field b * S2005S) ^ 2
        = algebraMap ℚ S1720Field q := by
      rw [← hab]; exact hyq
    rw [hsq] at h1
    rw [map_sub]
    linear_combination h1
  obtain ⟨hcoef, hcross⟩ := S2005_eq_zero_of_add_mul_S hkey
  have hab0 : a * b = 0 := by
    rcases mul_eq_zero.mp hcross with h | h
    · have ha : a = 0 := by linarith
      rw [ha, zero_mul]
    · rw [h, mul_zero]
  rcases mul_eq_zero.mp hab0 with ha | hb
  · refine ⟨b, ?_⟩
    have hy' : y = algebraMap ℚ S1720Field b * S2005S := by rw [hab, ha, map_zero, zero_add]
    rw [hy', mul_pow, S2005S_sq, ← map_pow]
    rw [show (-3 : S1720Field) = algebraMap ℚ S1720Field (-3) by norm_num, ← map_mul]
    congr 1
    ring
  · exfalso
    apply hybot
    rw [hab, hb, map_zero, zero_mul, add_zero]
    exact IntermediateField.algebraMap_mem ⊥ a

/-- An element of F' whose square is rational either lies in the copy of K, or is
i times an element of the copy of K. -/
theorem S2005_eq_or_mul_I_of_sq_mem (x : S1720Field)
    (hxsq : ∃ q : ℚ, x ^ 2 = algebraMap ℚ S1720Field q) :
    x ∈ S2005E ∨ ∃ b : S1720Field, b ∈ S2005E ∧ b ≠ 0 ∧ x = b * S2005I := by
  obtain ⟨a, haE, b, hbE, hxab⟩ := S2005_normal_form x
  obtain ⟨q, hxq⟩ := hxsq
  have hexp : (a + b * S2005I) ^ 2 = (a ^ 2 - b ^ 2) + (2 * a * b) * S2005I := by
    rw [add_sq, mul_pow, S2005I_sq]; ring
  have hmem : (a + b * S2005I) ^ 2 ∈ S2005E := by
    have h : (a + b * S2005I) ^ 2 = algebraMap ℚ S1720Field q := by
      rw [← hxab]; exact hxq
    rw [h]
    exact IntermediateField.algebraMap_mem S2005E q
  rw [hexp] at hmem
  have hcross : (2 * a * b) * S2005I ∈ S2005E := by
    have h1 : a ^ 2 - b ^ 2 ∈ S2005E :=
      sub_mem (pow_mem haE 2) (pow_mem hbE 2)
    have h2 := sub_mem hmem h1
    have h3 : (a ^ 2 - b ^ 2) + (2 * a * b) * S2005I - (a ^ 2 - b ^ 2)
        = (2 * a * b) * S2005I := by ring
    rwa [h3] at h2
  have hE2ab : 2 * a * b ∈ S2005E := by
    have h2 : (2 : S1720Field) ∈ S2005E := by
      rw [show (2 : S1720Field) = algebraMap ℚ S1720Field 2 by norm_num]
      exact IntermediateField.algebraMap_mem S2005E 2
    exact mul_mem (mul_mem h2 haE) hbE
  have hc : 2 * a * b = 0 := by
    by_contra h
    apply S2005I_notMem_E
    have h1 : S2005I = ((2 * a * b) * S2005I) / (2 * a * b) := by
      rw [eq_div_iff h]
      ring
    rw [h1]
    exact div_mem hcross hE2ab
  have hab' : a * b = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · rcases mul_eq_zero.mp h with h2 | h2
      · exact absurd h2 (by norm_num)
      · rw [h2, zero_mul]
    · rw [h, mul_zero]
  rcases mul_eq_zero.mp hab' with ha0 | hb0
  · by_cases hb0' : b = 0
    · left
      rw [hxab, ha0, hb0']
      simp
    · right
      exact ⟨b, hbE, hb0', by rw [hxab, ha0, zero_add]⟩
  · left
    rw [hxab, hb0]
    simp [haE]

/-- **The quadratic subfields of F' = SplittingField (S1687H * (X^2+1))**. -/
theorem S2005QuadraticSubfields : S1993QuadraticSubfields := by
  refine ⟨⟨S2005S, S2005S_sq⟩, ⟨S2005S * S2005I, ?_⟩, ⟨S2005I, S2005I_sq⟩, ?_⟩
  · rw [mul_pow, S2005S_sq, S2005I_sq]
    norm_num
  · intro x hxrange hxsq
    obtain ⟨q, hxq⟩ := hxsq
    have hxbot : x ∉ (⊥ : IntermediateField ℚ S1720Field) := by
      intro h
      exact hxrange (IntermediateField.mem_bot.mp h)
    rcases S2005_eq_or_mul_I_of_sq_mem x ⟨q, hxq⟩ with hxE | ⟨b, hbE, hb0, hxb⟩
    · obtain ⟨r, hr⟩ := S2005_sq_form_of_mem_E hxE q hxq hxbot
      exact Or.inl ⟨r, hr⟩
    · by_cases hbQ : b ∈ (⊥ : IntermediateField ℚ S1720Field)
      · rw [IntermediateField.mem_bot] at hbQ
        obtain ⟨c, hc⟩ := hbQ
        right; right
        refine ⟨c, ?_⟩
        rw [hxb, ← hc, mul_pow, S2005I_sq]
        rw [show (-1 : S1720Field) = algebraMap ℚ S1720Field (-1) by norm_num,
          ← map_pow, ← map_mul]
        congr 1
        ring
      · have hbq : b ^ 2 = algebraMap ℚ S1720Field (-q) := by
          have h1 : (b * S2005I) ^ 2 = algebraMap ℚ S1720Field q := by
            rw [← hxb]; exact hxq
          rw [mul_pow, S2005I_sq] at h1
          rw [map_neg]
          linear_combination -h1
        obtain ⟨r, hr⟩ := S2005_sq_form_of_mem_E hbE (-q) hbq hbQ
        have hq : q = 3 * r ^ 2 := by
          have h1 : algebraMap ℚ S1720Field (-q) = algebraMap ℚ S1720Field (-3 * r ^ 2) := by
            rw [← hbq, hr]
          have h2 : (-q : ℚ) = -3 * r ^ 2 := (algebraMap ℚ S1720Field).injective h1
          linarith
        exact Or.inr (Or.inl ⟨r, by rw [hxq, hq]⟩)


/-! ## 7. Axiom audit -/

#print axioms S2005E_finrank
#print axioms S2005_roots_H_mem_E
#print axioms S2005_no_sqrt_neg_one_in_E
#print axioms S2005_adjoin_E_I_eq_top
#print axioms S2005_finrank_over_E
#print axioms S2005_finrank
#print axioms S2005_gal_card
#print axioms S2005_gal_sqrt_card
#print axioms S2005FprimeGroupStructure
#print axioms S2005_quadratic_unique
#print axioms S2005_normal_form
#print axioms S2005_sq_form_of_mem_E
#print axioms S2005_eq_or_mul_I_of_sq_mem
#print axioms S2005QuadraticSubfields

end LeanFormal.IUT.XiFPaper.S2005FprimeGroupActual

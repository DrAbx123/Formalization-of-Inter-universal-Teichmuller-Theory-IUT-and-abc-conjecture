/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import tmp.sheaf.xif.paper.S1722DegreePrimeActual
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.LinearDisjoint

/-!
# S1993: the finite-group/Galois bridge for the D5 large-image input at l = 5

S1987 proved that the mathematical truth of the l = 5 large-image input on the
actual curve E'/F' follows from seven formalisation gaps, among them

* (5) Dickson's classification of the maximal subgroups of GL_2(F_5) together
  with the finite verification that the 12-element {+-P} action is transitive
  and that GL_2(F_5) contains an element of cycle type (10,2);
* (6) the Galois group of the S1687 polynomial and the quadratic subfields of
  F' = SplittingField (S1687H * (X^2 + 1)).

This file formalises the non-arithmetic part of (6) that is within reach of
Mathlib's Galois theory, and records exactly the remaining input as a
plain Prop (no axiom, no sorry, no inhabitant is manufactured).

## What is proved here (kernel-checked)

Let P = S1687P and K = SplittingField P.

* S1993P_irreducible : P is irreducible over Q.  Proof: the integer model of
  P has no root modulo 13 (checked case-by-case in ZMod 13), and the rational
  root theorem then rules out rational roots; a cubic with no rational root is
  irreducible.
* S1993Cubic_discr : the Mathlib cubic discriminant of P is -3 * r^2 for the
  explicit nonzero rational r = 2^34 * 3^4 * 5^4 * 7^4 * 19^3 * 1459.
* S1993SqrtNegThree_sq : K contains an explicit square root s of -3
  (S1993SqrtNegThree), obtained from Mathlib's
  Cubic.discr_eq_prod_three_roots and the discriminant computation.  This
  realises the quadratic subfield Q(sqrt(-3)) of K inside the kernel.
* S1993Alpha_minpoly / S1993_adjoin_alpha_finrank : for an actual root
  alpha of P in K, minpoly Q alpha = monicisation of P and [Q(alpha):Q] = 3.
* S1993SqrtNegThree_notMem_adjoin : sqrt(-3) is not in Q(alpha).
* S1993_adjoin_alpha_s_finrank : [Q(alpha, sqrt(-3)) : Q] = 6.
* S1993_finrank_K : [K : Q] = 6.
* S1993Gal_equiv_perm : Gal(K/Q) is isomorphic to the full symmetric group
  on the three roots of P, i.e. to S_3.
* S1993_sup_eq_top : K is generated over Q by alpha and sqrt(-3), i.e.
  K = Q(alpha) sup Q(sqrt(-3)).
* the explicit algebraic certificate S1993B_sq : B(alpha)^2 = -alpha/3.
  Writing s = sqrt(-3) and rho = B(alpha) * s, this gives rho^2 = alpha in K;
  rho is therefore a root of S1687H = P(X^2) inside K.  This is the remaining
  ingredient needed to show that K is a splitting field of S1687H.

The last point is the key bridge from the P-side (where the discriminant and
irreducibility are available) to the S1687H-side Galois group S_3.  The
splitting-field conclusion itself is NOT proved here; it is the first missing
statement S1993SplittingFieldH_eq below.  What IS available unconditionally
here is the implication S1993SplittingFieldH_eq -> [S1687Field:Q] = 6 and
Gal(S1687Field/Q) = S_3, see S1993S1687Field_finrank_of_splitting and
S1993Gal_S1687Field_of_splitting.

## What is not proved here: the exact first missing

The remaining part of (6) is the Galois group of

  F' = S1720Field = SplittingField (S1687H * (X^2 + 1))

and the classification of its quadratic subfields.  It is recorded below as

  S1993FprimeGroupStructure
  S1993QuadraticSubfields

and the conjunction S1993ExactFirstMissing.  These are plain propositions;
no inhabitant is produced.  The precise first missing step is
S1993SplittingFieldH_eq: K is a splitting field of S1687H (equivalently
S1687Field = SplittingField S1687H is Q-isomorphic to K).  All of the present
file's S_3 structure transfers across that single isomorphism.  The second
missing step is the F' product decomposition and the resulting classification
of the quadratic subfields of F' (the disjointness of K and Q(i) inside F',
which follows from S1993SplittingFieldH_eq and the degree count [F':Q] = 12).

## Verification status

The file compiles (EXIT 0) with no sorry, admit, axiom, opaque declaration,
native_decide or True/PUnit gate.  The axiom footprint of every main theorem is
propext, Classical.choice and Quot.sound only; see the #print axioms block at
the end.  The target of (6) is therefore only partially closed: the results
above are kernel-checked, the missing pieces are explicit Props.

## Consumers

* S1987D5LargeImageFiveActual (the l = 5 large-image endpoint), and through
  it S1982D5FiveActual / S1725SourceTorsionFPrimeActual;
* any later formalisation of (5) or of the division-field/Galois bridge (2)-(4)
  of the S1987 report, which needs the S_3 structure of the S1687 splitting
  field and the quadratic subfield Q(sqrt(-3)).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1722DegreePrimeActual
open scoped IntermediateField

/-! ## 0. The cubic model, the integer model, and the modulus-13 certificate -/

/-- The rational cubic whose roots are the x-coordinates of the residual cubic
of the 3-division polynomial (S1687P, exposed as a Mathlib Cubic). -/
def S1993Cubic : Cubic ℚ :=
  ⟨463856467968, 3973952045056, 1991485440000, 6153500390625⟩

/-- The cubic model is exactly the S1687 residual cubic. -/
theorem S1993Cubic_toPoly : S1993Cubic.toPoly = S1687P := by
  unfold S1993Cubic S1687P Cubic.toPoly
  ring

/-- The explicit rational square root of the discriminant: disc(P) = -3 * r^2. -/
def S1993R : ℤ := 2 ^ 34 * 3 ^ 4 * 5 ^ 4 * 7 ^ 4 * 19 ^ 3 * 1459

/-- The discriminant of P, computed with Mathlib's cubic discriminant. -/
theorem S1993Cubic_discr : S1993Cubic.discr = -3 * (S1993R : ℚ) ^ 2 := by
  unfold S1993Cubic Cubic.discr S1993R
  norm_num

/-- The integer model of P. -/
def S1993PZ : ℤ[X] :=
  C 463856467968 * X ^ 3 + C 3973952045056 * X ^ 2 +
    C 1991485440000 * X + C 6153500390625

/-- The integer model reduces to P over Q. -/
theorem S1993PZ_map : S1993PZ.map (Int.castRingHom ℚ) = S1687P := by
  unfold S1993PZ S1687P
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  norm_num

theorem S1993PZ_natDegree : S1993PZ.natDegree = 3 := by
  rw [show S1993PZ = C 463856467968 * X ^ 3 + C 3973952045056 * X ^ 2 +
      C 1991485440000 * X + C 6153500390625 from rfl]
  exact Polynomial.natDegree_cubic (by norm_num)

theorem S1993PZ_leadingCoeff : S1993PZ.leadingCoeff = 463856467968 := by
  rw [show S1993PZ = C 463856467968 * X ^ 3 + C 3973952045056 * X ^ 2 +
      C 1991485440000 * X + C 6153500390625 from rfl]
  exact Polynomial.leadingCoeff_cubic (by norm_num)

/-- The reduction of the integer model modulo 13. -/
def S1993PZ13 : (ZMod 13)[X] := S1993PZ.map (Int.castRingHom (ZMod 13))

theorem S1993PZ13_natDegree : S1993PZ13.natDegree = 3 := by
  unfold S1993PZ13
  rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
  · exact S1993PZ_natDegree
  · rw [S1993PZ_leadingCoeff]
    decide

/-- P has no root modulo 13.  This is the explicit finite certificate. -/
theorem S1993PZ13_noRoot : ∀ x : ZMod 13, ¬ S1993PZ13.IsRoot x := by
  intro x
  fin_cases x <;>
    (simp only [Polynomial.IsRoot, S1993PZ13, S1993PZ, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow] <;>
     decide)

/-! ## 1. P is irreducible over Q -/

/-- P has no rational root.  Proof: clear denominators (rational root theorem)
and reduce the resulting integer root equation modulo 13, where P has no root. -/
theorem S1993PZ_no_ratRoot (r : ℚ) (hr : aeval r S1993PZ = 0) : False := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let d : ℤ := IsFractionRing.den ℤ r
  let n : ℤ := IsFractionRing.num ℤ r
  have hdvd : d ∣ S1993PZ.leadingCoeff := den_dvd_of_is_root hr
  have h13c : ¬ (13 : ℤ) ∣ S1993PZ.leadingCoeff := by
    rw [S1993PZ_leadingCoeff]
    norm_num
  have h13d : ¬ (13 : ℤ) ∣ d := fun h => h13c (h.trans hdvd)
  have hd0 : (d : ZMod 13) ≠ 0 := by
    intro h
    exact h13d ((ZMod.intCast_zmod_eq_zero_iff_dvd d 13).mp h)
  have hroot : Polynomial.eval n (S1993PZ.scaleRoots d) = 0 := by
    have h := num_isRoot_scaleRoots_of_aeval_eq_zero (A := ℤ) (K := ℚ)
      (p := S1993PZ) (x := r) hr
    simpa [Polynomial.IsRoot, d, n] using h
  let ψ : ℤ →+* ZMod 13 := Int.castRingHom (ZMod 13)
  have hψlc : ψ S1993PZ.leadingCoeff ≠ 0 := by
    rw [S1993PZ_leadingCoeff]
    change ¬ ((463856467968 : ℤ) : ZMod 13) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  have hmap : (S1993PZ.scaleRoots d).map ψ =
      (S1993PZ.map ψ).scaleRoots (ψ d) := by
    rw [Polynomial.map_scaleRoots _ _ _ hψlc]
  have h1 : Polynomial.eval (n : ZMod 13)
      ((S1993PZ.map ψ).scaleRoots (ψ d)) = 0 := by
    rw [← hmap, Polynomial.eval_intCast_map]
    simpa using congrArg ψ hroot
  let t : ZMod 13 := (n : ZMod 13) / (ψ d)
  have hdt : ψ d * t = (n : ZMod 13) := by
    simp only [t]
    exact mul_div_cancel₀ _ hd0
  have h2 := Polynomial.scaleRoots_eval_mul (S1993PZ.map ψ) t (ψ d)
  rw [hdt] at h2
  have h3 : (ψ d) ^ (S1993PZ.map ψ).natDegree *
      Polynomial.eval t (S1993PZ.map ψ) = 0 := by
    rw [← h2]
    exact h1
  have h4 : Polynomial.eval t (S1993PZ.map ψ) = 0 := by
    exact (mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ hd0)
  exact S1993PZ13_noRoot t (by simpa [S1993PZ13, ψ] using h4)

/-- P has no rational root. -/
theorem S1993P_no_ratRoot (r : ℚ) : ¬ S1687P.IsRoot r := by
  intro hr
  apply S1993PZ_no_ratRoot r
  have h : aeval r S1993PZ = aeval r (S1993PZ.map (Int.castRingHom ℚ)) :=
    Polynomial.aeval_eq_aeval_map (by ext x; rfl) S1993PZ r
  rw [S1993PZ_map] at h
  rw [h]
  simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hr

/-- **P is irreducible over Q.** -/
theorem S1993P_irreducible : Irreducible S1687P := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [S1687P_natDegree]
    norm_num
  · intro x
    exact S1993P_no_ratRoot x

theorem S1993P_leadingCoeff : S1687P.leadingCoeff = 463856467968 := by
  unfold S1687P
  exact Polynomial.leadingCoeff_cubic (by norm_num)

/-- The monicisation of P. -/
def S1993Pmonic : ℚ[X] := S1687P * C ((S1687P.leadingCoeff)⁻¹)

theorem S1993Pmonic_monic : S1993Pmonic.Monic :=
  Polynomial.monic_mul_leadingCoeff_inv S1687P_ne_zero

theorem S1993Pmonic_irreducible : Irreducible S1993Pmonic :=
  Polynomial.irreducible_mul_leadingCoeff_inv.mpr S1993P_irreducible

theorem S1993Pmonic_natDegree : S1993Pmonic.natDegree = 3 := by
  rw [S1993Pmonic, Polynomial.natDegree_mul_leadingCoeff_inv _ S1687P_ne_zero,
    S1687P_natDegree]

/-! ## 2. The splitting field, a root, and sqrt(-3) -/

/-- The splitting field of P. -/
abbrev S1993KP : Type := Polynomial.SplittingField S1687P

instance S1993KP_finiteDimensional : FiniteDimensional ℚ S1993KP := by
  letI : IsSplittingField ℚ S1993KP S1687P :=
    Polynomial.IsSplittingField.splittingField S1687P
  exact Polynomial.IsSplittingField.finiteDimensional S1993KP S1687P

instance S1993KP_isGalois : IsGalois ℚ S1993KP := by
  letI : IsSplittingField ℚ S1993KP S1687P :=
    Polynomial.IsSplittingField.splittingField S1687P
  exact IsGalois.of_separable_splitting_field (p := S1687P) S1687P_separable

theorem S1993P_map_natDegree : (S1687P.map (algebraMap ℚ S1993KP)).natDegree = 3 := by
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ S1993KP).injective,
    S1687P_natDegree]

theorem S1993P_map_ne_zero : S1687P.map (algebraMap ℚ S1993KP) ≠ 0 := by
  intro h
  exact S1687P_ne_zero
    ((Polynomial.map_eq_zero_iff (algebraMap ℚ S1993KP).injective).mp h)

theorem S1993P_map_degree_ne_zero :
    (S1687P.map (algebraMap ℚ S1993KP)).degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree S1993P_map_ne_zero, S1993P_map_natDegree]
  norm_num

/-- An actual root of P in its splitting field. -/
noncomputable def S1993Alpha : S1993KP :=
  Polynomial.rootOfSplits (Polynomial.SplittingField.splits S1687P)
    S1993P_map_degree_ne_zero

theorem S1993Alpha_root : aeval S1993Alpha S1687P = 0 := by
  rw [show S1993Alpha = Polynomial.rootOfSplits
    (Polynomial.SplittingField.splits S1687P) S1993P_map_degree_ne_zero from rfl]
  rw [Polynomial.aeval_def, ← Polynomial.eval_map]
  exact Polynomial.eval_rootOfSplits _ _

theorem S1993Alpha_minpoly : minpoly ℚ S1993Alpha = S1993Pmonic := by
  have hp : aeval S1993Alpha S1993Pmonic = 0 := by
    simp [S1993Pmonic, S1993Alpha_root]
  exact (minpoly.eq_of_irreducible_of_monic (A := ℚ) (B := S1993KP)
    (x := S1993Alpha) (p := S1993Pmonic) S1993Pmonic_irreducible hp
    S1993Pmonic_monic).symm

theorem S1993Alpha_minpoly_natDegree : (minpoly ℚ S1993Alpha).natDegree = 3 := by
  rw [S1993Alpha_minpoly, S1993Pmonic_natDegree]

/-- [Q(alpha):Q] = 3. -/
theorem S1993_adjoin_alpha_finrank :
    Module.finrank ℚ (ℚ⟮S1993Alpha⟯ : IntermediateField ℚ S1993KP) = 3 := by
  rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ S1993Alpha),
    S1993Alpha_minpoly_natDegree]

/-- The three roots of P in its splitting field, from Mathlib's cubic API. -/
theorem S1993Cubic_roots_three :
    ∃ x y z : S1993KP, (Cubic.map (algebraMap ℚ S1993KP) S1993Cubic).roots = {x, y, z} := by
  have ha : S1993Cubic.a ≠ 0 := by
    show (463856467968 : ℚ) ≠ 0
    norm_num
  have hs : (Polynomial.map (algebraMap ℚ S1993KP) S1993Cubic.toPoly).Splits := by
    rw [S1993Cubic_toPoly]
    exact Polynomial.SplittingField.splits S1687P
  exact (Cubic.splits_iff_roots_eq_three (P := S1993Cubic)
    (φ := algebraMap ℚ S1993KP) ha).mp hs

/-- The discriminant identity for the three roots. -/
theorem S1993Cubic_delta_sq (x y z : S1993KP)
    (h3 : (Cubic.map (algebraMap ℚ S1993KP) S1993Cubic).roots = {x, y, z}) :
    (algebraMap ℚ S1993KP S1993Cubic.a * algebraMap ℚ S1993KP S1993Cubic.a *
      (x - y) * (x - z) * (y - z)) ^ 2
        = -3 * (algebraMap ℚ S1993KP (S1993R : ℚ)) ^ 2 := by
  have ha : S1993Cubic.a ≠ 0 := by
    show (463856467968 : ℚ) ≠ 0
    norm_num
  have h := Cubic.discr_eq_prod_three_roots (P := S1993Cubic)
    (φ := algebraMap ℚ S1993KP) ha h3
  have h2 : algebraMap ℚ S1993KP S1993Cubic.discr =
      algebraMap ℚ S1993KP (-3 * (S1993R : ℚ) ^ 2) := by
    rw [S1993Cubic_discr]
  rw [h2] at h
  rw [← h]
  simp only [map_neg, map_mul, map_pow, map_ofNat]

/-- **There is a square root of -3 in the splitting field of P.** -/
theorem S1993SqrtNegThree_exists : ∃ s : S1993KP, s ^ 2 = (-3 : S1993KP) := by
  classical
  obtain ⟨x, y, z, h3⟩ := S1993Cubic_roots_three
  refine ⟨algebraMap ℚ S1993KP S1993Cubic.a * algebraMap ℚ S1993KP S1993Cubic.a *
      (x - y) * (x - z) * (y - z) /
      algebraMap ℚ S1993KP (S1993R : ℚ), ?_⟩
  have hδ : (algebraMap ℚ S1993KP S1993Cubic.a *
      algebraMap ℚ S1993KP S1993Cubic.a *
      (x - y) * (x - z) * (y - z)) ^ 2
        = -3 * (algebraMap ℚ S1993KP (S1993R : ℚ)) ^ 2 :=
    S1993Cubic_delta_sq x y z h3
  have hr0 : algebraMap ℚ S1993KP (S1993R : ℚ) ≠ 0 := by
    have hR : (S1993R : ℚ) ≠ 0 := by
      unfold S1993R
      norm_num
    exact map_ne_zero_of_mem_nonZeroDivisors _ (algebraMap ℚ S1993KP).injective
      (mem_nonZeroDivisors_iff_ne_zero.mpr hR)
  rw [div_pow, hδ]
  field_simp

/-- An explicit square root of -3 in the splitting field of P. -/
noncomputable def S1993SqrtNegThree : S1993KP :=
  Classical.choose S1993SqrtNegThree_exists

/-- The square of the explicit square root of -3 is -3. -/
theorem S1993SqrtNegThree_sq : S1993SqrtNegThree ^ 2 = (-3 : S1993KP) :=
  Classical.choose_spec S1993SqrtNegThree_exists


/-! ## 3. [K : Q] = 6 and Gal(K/Q) = S_3 -/

/-- The minimal polynomial of the explicit sqrt(-3) is X^2 + 3. -/
theorem S1993SqrtNegThree_minpoly :
    minpoly ℚ S1993SqrtNegThree = X ^ 2 + C (3 : ℚ) := by
  have hirr : Irreducible (X ^ 2 + C (3 : ℚ) : ℚ[X]) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (p := X ^ 2 + C (3 : ℚ)) ?_ ?_
    · simp
    · intro x hx
      simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] at hx
      nlinarith [sq_nonneg x]
  have haeval : aeval S1993SqrtNegThree (X ^ 2 + C (3 : ℚ) : ℚ[X]) = 0 := by
    simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [S1993SqrtNegThree_sq]
    norm_num
  have hmonic : (X ^ 2 + C (3 : ℚ) : ℚ[X]).Monic :=
    Polynomial.monic_X_pow_add_C (a := (3 : ℚ)) (n := 2) (by norm_num)
  exact (minpoly.eq_of_irreducible_of_monic (A := ℚ) (B := S1993KP)
    (x := S1993SqrtNegThree) (p := X ^ 2 + C (3 : ℚ)) hirr haeval hmonic).symm

/-- [Q(sqrt(-3)) : Q] = 2. -/
theorem S1993_adjoin_s_finrank :
    Module.finrank ℚ (ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP) = 2 := by
  rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ S1993SqrtNegThree),
    S1993SqrtNegThree_minpoly]
  simp

/-- The quadratic subfield Q(sqrt(-3)) divides [K : Q]. -/
theorem S1993_two_dvd_finrank : 2 ∣ Module.finrank ℚ S1993KP := by
  have ht := Module.finrank_mul_finrank ℚ
    (ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP) S1993KP
  rw [S1993_adjoin_s_finrank] at ht
  exact ⟨_, ht.symm⟩

/-- The cubic subfield Q(alpha) divides [K : Q]. -/
theorem S1993_three_dvd_finrank : 3 ∣ Module.finrank ℚ S1993KP := by
  have ht := Module.finrank_mul_finrank ℚ
    (ℚ⟮S1993Alpha⟯ : IntermediateField ℚ S1993KP) S1993KP
  rw [S1993_adjoin_alpha_finrank] at ht
  exact ⟨_, ht.symm⟩

/-- 6 divides [K : Q]. -/
theorem S1993_six_dvd_finrank : 6 ∣ Module.finrank ℚ S1993KP := by
  have h := (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 2)
    S1993_three_dvd_finrank S1993_two_dvd_finrank)
  simpa using h

/-- The number of roots of P in its splitting field is 3. -/
theorem S1993P_card_rootSet : Nat.card (S1687P.rootSet S1993KP) = 3 := by
  have h := Polynomial.card_rootSet_eq_natDegree (K := S1993KP) S1687P_separable
    (Polynomial.SplittingField.splits S1687P)
  rw [S1687P_natDegree] at h
  exact Nat.card_eq_fintype_card.trans h

/-- The Galois group of K acts faithfully on the three roots, so it has at most
6 elements. -/
theorem S1993Gal_card_le : Nat.card (S1687P.Gal) ≤ 6 := by
  haveI : Fact ((S1687P.map (algebraMap ℚ S1993KP)).Splits) :=
    ⟨Polynomial.SplittingField.splits S1687P⟩
  have hinj := Polynomial.Gal.galActionHom_injective S1687P S1993KP
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_perm, S1993P_card_rootSet] at hle
  norm_num at hle
  simpa using hle

/-- **[K : Q] = 6.** -/
theorem S1993_finrank_K : Module.finrank ℚ S1993KP = 6 := by
  have hcard : Nat.card (S1687P.Gal) = Nat.card (S1993KP ≃ₐ[ℚ] S1993KP) := rfl
  have hupper : Module.finrank ℚ S1993KP ≤ 6 := by
    have h := (IsGalois.card_aut_eq_finrank ℚ S1993KP).symm
    rw [h, ← hcard]
    exact S1993Gal_card_le
  obtain ⟨m, hm⟩ := S1993_six_dvd_finrank
  have hpos : 0 < Module.finrank ℚ S1993KP := Module.finrank_pos
  omega

/-- **The Galois group of K is S_3**: it is the full permutation group on the
three roots of P. -/
theorem S1993Gal_equiv_perm :
    Nonempty (Polynomial.Gal S1687P ≃*
      Equiv.Perm (S1687P.rootSet S1993KP)) := by
  haveI : Fact ((S1687P.map (algebraMap ℚ S1993KP)).Splits) :=
    ⟨Polynomial.SplittingField.splits S1687P⟩
  have hinj := Polynomial.Gal.galActionHom_injective S1687P S1993KP
  have hfin : Nat.card (S1687P.Gal) = Nat.card (Equiv.Perm (S1687P.rootSet S1993KP)) := by
    rw [Nat.card_perm, S1993P_card_rootSet]
    rw [Polynomial.Gal.card_of_separable S1687P_separable, S1993_finrank_K]
    norm_num
  have hbij : Function.Bijective (Polynomial.Gal.galActionHom S1687P S1993KP) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hfin⟩
  exact ⟨MulEquiv.ofBijective _ hbij⟩

/-- Q(alpha) and Q(sqrt(-3)) have coprime degrees 3 and 2, hence are linearly
disjoint and their compositum has degree 6. -/
theorem S1993_adjoin_alpha_s_finrank :
    Module.finrank ℚ (ℚ⟮S1993Alpha⟯ ⊔ ℚ⟮S1993SqrtNegThree⟯ :
      IntermediateField ℚ S1993KP) = 6 := by
  have hcop : Nat.Coprime
      (Module.finrank ℚ (ℚ⟮S1993Alpha⟯ : IntermediateField ℚ S1993KP))
      (Module.finrank ℚ (ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP)) := by
    rw [S1993_adjoin_alpha_finrank, S1993_adjoin_s_finrank]
    norm_num
  have hdisj := IntermediateField.LinearDisjoint.of_finrank_coprime
    (A := (ℚ⟮S1993Alpha⟯ : IntermediateField ℚ S1993KP))
    (L := (ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP)) hcop
  rw [hdisj.finrank_sup, S1993_adjoin_alpha_finrank, S1993_adjoin_s_finrank]

/-- Q(alpha) and Q(sqrt(-3)) generate K over Q. -/
theorem S1993_sup_eq_top :
    (ℚ⟮S1993Alpha⟯ ⊔ ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP) = ⊤ := by
  apply IntermediateField.eq_of_le_of_finrank_eq le_top
  rw [S1993_adjoin_alpha_s_finrank, IntermediateField.finrank_top', S1993_finrank_K]

/-- **K = Q(alpha, sqrt(-3))**: the splitting field of P is generated by the
root alpha and the explicit sqrt(-3). -/
theorem S1993KP_eq_adjoin_alpha_s :
    (ℚ⟮S1993Alpha⟯ ⊔ ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP) = ⊤ :=
  S1993_sup_eq_top

/-- sqrt(-3) is not in Q(alpha). -/
theorem S1993SqrtNegThree_notMem_adjoin :
    S1993SqrtNegThree ∉ (ℚ⟮S1993Alpha⟯ : IntermediateField ℚ S1993KP) := by
  intro hmem
  have hle : (ℚ⟮S1993SqrtNegThree⟯ : IntermediateField ℚ S1993KP) ≤
      ℚ⟮S1993Alpha⟯ := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hmem
  have hsup : (ℚ⟮S1993Alpha⟯ ⊔ ℚ⟮S1993SqrtNegThree⟯ :
      IntermediateField ℚ S1993KP) = ℚ⟮S1993Alpha⟯ := sup_eq_left.mpr hle
  rw [S1993_sup_eq_top] at hsup
  have hfin : Module.finrank ℚ (⊤ : IntermediateField ℚ S1993KP) = 3 := by
    rw [hsup, S1993_adjoin_alpha_finrank]
  rw [IntermediateField.finrank_top', S1993_finrank_K] at hfin
  norm_num at hfin

/-! ## 4. The explicit square-root certificate for S1687H = P(X^2) -/

/-- The polynomial B with B(alpha)^2 = -alpha/3 at every root alpha of P. -/
def S1993B : ℚ[X] :=
  C (-3675 / 11672) + C (359552 / 984825) * X + C (131072 / 1787275) * X ^ 2

/-- The quotient witnessing B^2 + X/3 = P * Q. -/
def S1993Q : ℚ[X] :=
  C (1 / 62072337960000) + C (1 / 86247501991875) * X

/-- The polynomial identity: B^2 + X/3 = P * Q. -/
theorem S1993Cert : S1993B ^ 2 + C (1 / 3) * X = S1687P * S1993Q := by
  apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
  simp only [S1993B, S1993Q, S1687P, map_add, map_mul, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  norm_num
  ring

/-- **The certificate**: at any root alpha of P, B(alpha)^2 = -alpha/3. -/
theorem S1993B_sq {L : Type*} [Field L] [Algebra ℚ L] [CharZero L] (α : L)
    (hα : aeval α S1687P = 0) : (aeval α S1993B) ^ 2 = -(α / 3) := by
  have h := congrArg (aeval α) S1993Cert
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X] at h
  rw [hα, zero_mul] at h
  have h1 : (algebraMap ℚ L) (1 / 3) = (1 / 3 : L) := by norm_num
  rw [h1] at h
  linear_combination h

/-! ## 5. The reusable interface and the exact first missing -/

/-- The first missing bridge of (6): K = SplittingField P is a splitting field
of S1687H = P.comp (X^2), equivalently S1687Field = SplittingField S1687H is
Q-isomorphic to K.  All the S_3 structure proved above transfers across this
single isomorphism. -/
def S1993SplittingFieldH_eq : Prop :=
  Nonempty (S1687Field ≃ₐ[ℚ] S1993KP)

/-- The Galois-group part of (6) for F' = SplittingField (S1687H * (X^2+1)):
the Galois group is the direct product of the S1687H-part and the part of
X^2+1.  This is the precise statement that Gal(F'/Q) = S_3 x C_2 once the two
factors are identified. -/
def S1993FprimeGroupStructure : Prop :=
  Nonempty (Polynomial.Gal S1720H ≃*
    (Polynomial.Gal S1687H × Polynomial.Gal S1720SqrtPolynomial))

/-- The quadratic-subfield part of (6): F' contains square roots of -3, 3 and
-1, and every quadratic subfield of F' is one of the three generated by them.
A quadratic subfield is generated by an element x with x^2 = q in Q; it is
Q(sqrt(-3)) (resp. Q(sqrt(3)), resp. Q(i)) exactly when q/(-3) (resp. q/3,
resp. q/(-1)) is a rational square. -/
def S1993QuadraticSubfields : Prop :=
  (∃ s : S1720Field, s ^ 2 = (-3 : S1720Field)) ∧
  (∃ s : S1720Field, s ^ 2 = (3 : S1720Field)) ∧
  (∃ s : S1720Field, s ^ 2 = (-1 : S1720Field)) ∧
  ∀ x : S1720Field, x ∉ Set.range (algebraMap ℚ S1720Field) →
    (∃ q : ℚ, x ^ 2 = algebraMap ℚ S1720Field q) →
    (∃ r : ℚ, x ^ 2 = algebraMap ℚ S1720Field (-3 * r ^ 2)) ∨
    (∃ r : ℚ, x ^ 2 = algebraMap ℚ S1720Field (3 * r ^ 2)) ∨
    (∃ r : ℚ, x ^ 2 = algebraMap ℚ S1720Field (-1 * r ^ 2))

/-- The exact first missing of (6) in this file: the splitting-field bridge
and the Galois group of F'.  The quadratic-subfield statement is a consequence
of the group structure via the Galois correspondence; it is kept as a separate
named statement for downstream consumers. -/
def S1993ExactFirstMissing : Prop :=
  S1993SplittingFieldH_eq ∧ S1993FprimeGroupStructure

/-- Under the first bridge, [S1687Field : Q] = 6. -/
theorem S1993S1687Field_finrank_of_splitting (h : S1993SplittingFieldH_eq) :
    Module.finrank ℚ S1687Field = 6 := by
  obtain ⟨e⟩ := h
  have hlin := e.toLinearEquiv.finrank_eq
  rw [hlin, S1993_finrank_K]

/-- Under the first bridge, the Galois group of S1687H is S_3 (the full
permutation group on the three roots of P). -/
theorem S1993Gal_S1687Field_of_splitting (h : S1993SplittingFieldH_eq) :
    Nonempty (Polynomial.Gal S1687H ≃*
      Equiv.Perm (S1687P.rootSet S1993KP)) := by
  obtain ⟨e⟩ := h
  obtain ⟨g⟩ := S1993Gal_equiv_perm
  exact ⟨e.autCongr.trans g⟩

#print axioms S1993P_irreducible
#print axioms S1993SqrtNegThree_sq
#print axioms S1993_adjoin_alpha_s_finrank
#print axioms S1993_sup_eq_top
#print axioms S1993SqrtNegThree_notMem_adjoin
#print axioms S1993_finrank_K
#print axioms S1993Gal_equiv_perm
#print axioms S1993B_sq
#print axioms S1993S1687Field_finrank_of_splitting
#print axioms S1993Gal_S1687Field_of_splitting

end LeanFormal.IUT.XiFPaper.S1993D5FiniteGroupBridgeActual


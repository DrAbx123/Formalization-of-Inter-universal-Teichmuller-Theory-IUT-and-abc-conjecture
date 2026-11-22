/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36OddTorsionFiniteness
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# General odd division-polynomial degree and root bounds for y^2 = x^3 - x

Foundation F4d (general odd division-polynomial degree/root foundations).  This
module uses Mathlib's general degree formulas for the odd division polynomials
prePsi_n to prove, for the concrete curve y^2 = x^3 - x over a field K:

* the actual degree formula natDegree(prePsi_n) = (n^2 - 1)/2 for odd n with
  (n : K) != 0, and the nonzero leading coefficient (n : K), hence prePsi_n != 0;
* the root-count bound: prePsi_n has at most (n^2 - 1)/2 roots, so the odd
  division polynomial defines at most that many x-values; the root set is finite;
* the evaluation facts: for odd n, at every solution (x,y) of the curve the
  bivariate psi_n(x,y) equals prePsi_n(x), and at a nonsingular point the
  point-level evaluation equals prePsi_n(x);
* the conditional finiteness statement: IF the general group-law criterion
  n • P = 0 <-> psi_n(P) = 0 holds (frozen as
  oddNsmulDivisionPolynomialCriterionCard), THEN the actual n-torsion subgroup
  is finite.  The proof constructs the finite candidate set (point at infinity,
  roots x of prePsi_n, at most two y per x) and shows that, under the criterion,
  it contains the n-torsion subgroup.  No general odd torsion finiteness is
  claimed unconditionally.

## Honest boundary

The group-law-to-division-polynomial bridge for odd n > 3 is NOT proved here
and is NOT assumed silently: it is an explicit hypothesis of the conditional
finiteness theorem and is frozen as oddNsmulDivisionPolynomialCriterionCard.
Only the n = 3 case is proved in the task-72 module.  The degree and root-count
results are unconditional (Mathlib Degree.lean), but they are statements about
the division polynomial, not about torsion points.  No Tate module, inverse
limit, theta/q-pilot or Anabelian statement is made.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace OddDivisionPolynomialBounds

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.DivisionTorsionThree
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OddTorsionFiniteness

variable {K : Type*} [Field K]

/-! ## Degree, leading coefficient and nonvanishing of prePsi_n for odd n -/

/-- Odd natural numbers are not even when viewed as integers. -/
theorem not_even_int_of_odd {n : ℕ} (hodd : Odd n) : ¬ Even (n : ℤ) := by
  rw [Int.even_coe_nat]
  exact Nat.not_even_iff_odd.mpr hodd

/-- The actual degree of prePsi_n for odd n: (n^2 - 1)/2. -/
theorem y2x3xCurve_preΨ_natDegree_odd {n : ℕ} (hodd : Odd n) (hn : (n : K) ≠ 0) :
    ((y2x3xCurve (K := K)).preΨ (n : ℤ)).natDegree = (n ^ 2 - 1) / 2 := by
  have hnZ : ((n : ℤ) : K) ≠ 0 := by simpa using hn
  rw [WeierstrassCurve.natDegree_preΨ (W := y2x3xCurve (K := K))
    (n := (n : ℤ)) hnZ]
  rw [if_neg (not_even_int_of_odd hodd)]
  simp

/-- The leading coefficient of prePsi_n for odd n is n. -/
theorem y2x3xCurve_preΨ_leadingCoeff_odd {n : ℕ} (hodd : Odd n) (hn : (n : K) ≠ 0) :
    ((y2x3xCurve (K := K)).preΨ (n : ℤ)).leadingCoeff = (n : K) := by
  have hnZ : ((n : ℤ) : K) ≠ 0 := by simpa using hn
  rw [WeierstrassCurve.leadingCoeff_preΨ (W := y2x3xCurve (K := K))
    (n := (n : ℤ)) hnZ]
  rw [if_neg (not_even_int_of_odd hodd)]
  norm_cast

/-- The leading coefficient of prePsi_n for odd n is nonzero. -/
theorem y2x3xCurve_preΨ_leadingCoeff_ne_zero_odd {n : ℕ} (hodd : Odd n)
    (hn : (n : K) ≠ 0) :
    ((y2x3xCurve (K := K)).preΨ (n : ℤ)).leadingCoeff ≠ 0 := by
  rw [y2x3xCurve_preΨ_leadingCoeff_odd hodd hn]
  exact hn

/-- prePsi_n is nonzero for odd n. -/
theorem y2x3xCurve_preΨ_ne_zero_odd {n : ℕ} (hodd : Odd n) (hn : (n : K) ≠ 0) :
    (y2x3xCurve (K := K)).preΨ (n : ℤ) ≠ 0 :=
  WeierstrassCurve.preΨ_ne_zero (W := y2x3xCurve (K := K))
    (n := (n : ℤ)) (by simpa using hn)

/-- prePsi_n is nonzero whenever n is nonzero in K (no parity hypothesis). -/
theorem y2x3xCurve_preΨ_ne_zero {n : ℕ} (hn : (n : K) ≠ 0) :
    (y2x3xCurve (K := K)).preΨ (n : ℤ) ≠ 0 :=
  WeierstrassCurve.preΨ_ne_zero (W := y2x3xCurve (K := K))
    (n := (n : ℤ)) (by simpa using hn)

/-- Root-count bound: prePsi_n has at most (n^2 - 1)/2 roots for odd n. -/
theorem y2x3xCurve_preΨ_roots_card_le_odd {n : ℕ} (hodd : Odd n)
    (hn : (n : K) ≠ 0) :
    ((y2x3xCurve (K := K)).preΨ (n : ℤ)).roots.card ≤ (n ^ 2 - 1) / 2 := by
  refine (Polynomial.card_roots' _).trans ?_
  rw [y2x3xCurve_preΨ_natDegree_odd hodd hn]

/-- The root set of prePsi_n is finite for odd n. -/
theorem y2x3xCurve_preΨ_roots_finite_odd {n : ℕ} (hodd : Odd n)
    (hn : (n : K) ≠ 0) :
    Set.Finite {x : K | ((y2x3xCurve (K := K)).preΨ (n : ℤ)).IsRoot x} :=
  Polynomial.finite_setOf_isRoot (y2x3xCurve_preΨ_ne_zero_odd hodd hn)

/-! ## Evaluation facts for odd n -/

/-- For odd n, psi_n(x,y) equals prePsi_n(x) at every solution of the curve. -/
theorem y2x3xCurve_evalDivisionPolynomial_odd {n : ℕ} (hodd : Odd n) {x y : K}
    (h : (y2x3xCurve (K := K)).toAffine.Equation x y) :
    (y2x3xCurve (K := K)).evalDivisionPolynomial x y (n : ℤ) =
      ((y2x3xCurve (K := K)).preΨ (n : ℤ)).eval x :=
  WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd
    (y2x3xCurve (K := K)) h (not_even_int_of_odd hodd)

/-- For odd n, the point-level evaluation of psi_n equals prePsi_n(x) at a
nonsingular affine point. -/
theorem y2x3xCurve_evalDivisionPolynomialAtPoint_odd {n : ℕ} (hodd : Odd n)
    {x y : K} (h : (y2x3xCurve (K := K)).toAffine.Nonsingular x y) :
    (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint (n : ℤ)
        (WeierstrassCurve.Affine.Point.some x y h) =
      ((y2x3xCurve (K := K)).preΨ (n : ℤ)).eval x := by
  rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
    y2x3xCurve_evalDivisionPolynomial_odd hodd h.1]

/-! ## The frozen group-law criterion card -/

/-- **Frozen card: the general odd group-law criterion.**  For every field K
with 2 != 0, every odd n > 3 with n != 0 in K, and every affine point P, the
point P is n-torsion if and only if psi_n vanishes at P.  This is the missing
group-law-to-division-polynomial bridge for odd n > 3; only n = 3 is proved in
Example36DivisionTorsionThree.lean.  This is a card, not a theorem, and it is
not consumed. -/
def oddNsmulDivisionPolynomialCriterionCard : Prop :=
  ∀ (K : Type*) [Field K] [DecidableEq K], (2 : K) ≠ 0 →
    ∀ (n : ℕ), Odd n → 3 < n → (n : K) ≠ 0 →
      ∀ P : (y2x3xCurve (K := K)).toAffine.Point,
        (n : ℕ) • P = 0 ↔
          (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint (n : ℤ) P = 0

/-- A solution of y^2 = x^3 - x is a nonsingular point when 2 != 0: the only
possible singular points would have y = 0, hence x in {0,1,-1}, where the
partial derivative 3x^2 - 1 is -1 or 2. -/
theorem y2x3xCurve_nonsingular_of_sq (h2 : (2 : K) ≠ 0) {x y : K}
    (hy2 : y ^ 2 = x ^ 3 - x) :
    (y2x3xCurve (K := K)).toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨y2x3xCurve_equation_of_sq x y hy2, ?_⟩
  by_cases hy0 : y = 0
  · left
    have hx3 : x ^ 3 - x = 0 := by rw [← hy2, hy0]; ring
    have hfac : x * (x - 1) * (x + 1) = 0 := by
      have h : x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
      rwa [h]
    simp only [y2x3xCurve_a1, y2x3xCurve_a2, y2x3xCurve_a4]
    rcases mul_eq_zero.mp hfac with hx | hx
    · rcases mul_eq_zero.mp hx with hx0 | hx1
      · subst hx0
        intro hzero
        have h1 : (1 : K) = 0 := by linear_combination hzero
        exact one_ne_zero h1
      · have hxone : x = 1 := by linear_combination hx1
        subst hxone
        intro hzero
        have h2zero : (2 : K) = 0 := by linear_combination -hzero
        exact h2 h2zero
    · have hxneg : x = -1 := by linear_combination hx
      subst hxneg
      intro hzero
      have h2zero : (2 : K) = 0 := by linear_combination -hzero
      exact h2 h2zero
  · right
    simp only [y2x3xCurve_a1, y2x3xCurve_a3]
    intro hneg
    apply hy0
    have h2y : (2 : K) * y = 0 := by linear_combination hneg
    exact (mul_eq_zero.mp h2y).resolve_left h2

section ConditionalFiniteness

variable [DecidableEq K]

/-! ## Conditional finiteness of the odd torsion subgroup -/


/-- A root of prePsi_n in its root finset evaluates to zero. -/
theorem y2x3xCurve_preΨ_eval_of_mem_roots {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : x ∈ ((y2x3xCurve (K := K)).preΨ (n : ℤ)).roots.toFinset) :
    ((y2x3xCurve (K := K)).preΨ (n : ℤ)).eval x = 0 := by
  rw [Multiset.mem_toFinset,
    Polynomial.mem_roots (y2x3xCurve_preΨ_ne_zero (K := K) hn)] at hx
  exact hx

/-- The finite index set for odd n: a root x of prePsi_n together with a root
y of Y^2 - (x^3 - x). -/
noncomputable abbrev oddTorsionCandidateIndex (K : Type*) [Field K] [DecidableEq K]
    (n : ℕ) : Type _ :=
  Σ x : {x : K // x ∈ ((y2x3xCurve (K := K)).preΨ (n : ℤ)).roots.toFinset},
    {y : K // y ∈
      (Polynomial.X ^ 2 - Polynomial.C (x.1 ^ 3 - x.1) : K[X]).roots.toFinset}

/-- The candidate nonsingular affine point attached to a root pair (x, y). -/
noncomputable def oddTorsionCandidatePoint (h2 : (2 : K) ≠ 0) (n : ℕ) :
    oddTorsionCandidateIndex K n → (y2x3xCurve (K := K)).toAffine.Point :=
  fun p =>
    WeierstrassCurve.Affine.Point.some p.1.1 p.2.1
      (y2x3xCurve_nonsingular_of_sq h2 (y2x3xCurve_y_sq_of_mem_roots p.2.2))

/-- The explicit finite set of candidates for the odd n-torsion: the point at
infinity and all candidate affine points (x, y) with prePsi_n(x) = 0 and
y^2 = x^3 - x. -/
noncomputable def oddTorsionCandidates (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Finset ((y2x3xCurve (K := K)).toAffine.Point) :=
  insert 0 (Finset.univ.image (oddTorsionCandidatePoint (K := K) h2 n))

/-- Membership in the torsion-by-n subgroup is the group-law condition. -/
theorem mem_torsionBy_iff {n : ℤ}
    (P : (y2x3xCurve (K := K)).toAffine.Point) :
    P ∈ AddSubgroup.torsionBy (y2x3xCurve (K := K)).toAffine.Point n ↔
      n • P = 0 :=
  Iff.rfl

/-- Under the frozen odd group-law criterion, every candidate point is an
actual n-torsion point. -/
theorem oddTorsionCandidatePoint_mem (h2 : (2 : K) ≠ 0) {n : ℕ}
    (hodd : Odd n) (hn : (n : K) ≠ 0)
    (hcrit : ∀ P : (y2x3xCurve (K := K)).toAffine.Point,
      (n : ℕ) • P = 0 ↔
        (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint (n : ℤ) P = 0)
    (p : oddTorsionCandidateIndex K n) :
    oddTorsionCandidatePoint (K := K) h2 n p ∈
      AddSubgroup.torsionBy (y2x3xCurve (K := K)).toAffine.Point (n : ℤ) := by
  rw [mem_torsionBy_iff]
  rw [natCast_zsmul]
  refine (hcrit _).mpr ?_
  simp only [oddTorsionCandidatePoint]
  cases p with
  | mk x y =>
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      y2x3xCurve_evalDivisionPolynomial_odd hodd
        (y2x3xCurve_nonsingular_of_sq h2 (y2x3xCurve_y_sq_of_mem_roots y.2)).1]
    exact y2x3xCurve_preΨ_eval_of_mem_roots hn x.2

/-- **Conditional equality.**  If the frozen odd group-law criterion holds for
n, then the actual n-torsion subgroup equals the explicit finite candidate
set. -/
theorem torsionBy_eq_oddTorsionCandidates (h2 : (2 : K) ≠ 0) {n : ℕ}
    (hodd : Odd n) (hn : (n : K) ≠ 0)
    (hcrit : ∀ P : (y2x3xCurve (K := K)).toAffine.Point,
      (n : ℕ) • P = 0 ↔
        (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint (n : ℤ) P = 0) :
    (AddSubgroup.torsionBy (y2x3xCurve (K := K)).toAffine.Point (n : ℤ) : Set
        ((y2x3xCurve (K := K)).toAffine.Point)) =
      ↑(oddTorsionCandidates (K := K) h2 n) := by
  ext P
  constructor
  · intro hP
    have hsmul : (n : ℕ) • P = 0 := by
      have h' : (n : ℤ) • P = 0 := (mem_torsionBy_iff P).mp hP
      rw [natCast_zsmul] at h'
      exact h'
    have hP' : (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint
        (n : ℤ) P = 0 := (hcrit P).mp hsmul
    rw [Finset.mem_coe]
    cases P with
    | zero =>
      rw [oddTorsionCandidates, Finset.mem_insert]
      exact Or.inl rfl
    | some x y hns =>
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        y2x3xCurve_evalDivisionPolynomial_odd hodd hns.1] at hP'
      have hxmem : x ∈ ((y2x3xCurve (K := K)).preΨ (n : ℤ)).roots.toFinset := by
        rw [Multiset.mem_toFinset,
          Polynomial.mem_roots (y2x3xCurve_preΨ_ne_zero (K := K) hn)]
        exact hP'
      have hy2 : y ^ 2 = x ^ 3 - x :=
        y2x3xCurve_equation (K := K) x y hns.1
      have hymem : y ∈
          (Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) : K[X]).roots.toFinset := by
        have hne : (Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) : K[X]) ≠ 0 :=
          Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 2) (x ^ 3 - x)
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
        have hzero : y ^ 2 - (x ^ 3 - x) = 0 := by rw [hy2]; ring
        simpa [Polynomial.IsRoot] using hzero
      rw [oddTorsionCandidates, Finset.mem_insert, Finset.mem_image]
      right
      refine ⟨⟨⟨x, hxmem⟩, ⟨y, hymem⟩⟩, Finset.mem_univ _, ?_⟩
      simp only [oddTorsionCandidatePoint]
  · intro hP
    rw [Finset.mem_coe, oddTorsionCandidates, Finset.mem_insert,
      Finset.mem_image] at hP
    rcases hP with rfl | ⟨p, _, hp⟩
    · exact (mem_torsionBy_iff (0 : (y2x3xCurve (K := K)).toAffine.Point)).mpr
        (by simp)
    · rw [← hp]
      exact oddTorsionCandidatePoint_mem h2 hodd hn hcrit p

/-- **Conditional finiteness.**  Under the frozen odd group-law criterion, the
actual n-torsion subgroup is finite. -/
theorem torsionBy_finite_of_oddNsmulCriterion (h2 : (2 : K) ≠ 0) {n : ℕ}
    (hodd : Odd n) (hn : (n : K) ≠ 0)
    (hcrit : ∀ P : (y2x3xCurve (K := K)).toAffine.Point,
      (n : ℕ) • P = 0 ↔
        (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint (n : ℤ) P = 0) :
    Finite (AddSubgroup.torsionBy (y2x3xCurve (K := K)).toAffine.Point (n : ℤ)) := by
  have hfin : ((AddSubgroup.torsionBy (y2x3xCurve (K := K)).toAffine.Point
      (n : ℤ) : Set ((y2x3xCurve (K := K)).toAffine.Point))).Finite := by
    rw [torsionBy_eq_oddTorsionCandidates (K := K) h2 hodd hn hcrit]
    exact (oddTorsionCandidates (K := K) h2 n).finite_toSet
  exact hfin.to_subtype

end ConditionalFiniteness

end OddDivisionPolynomialBounds
end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- Audit record for Foundation F4d: general odd division-polynomial degree and
root bounds, and the conditional odd torsion finiteness. -/
def example36OddDivisionPolynomialBounds : Obligation :=
  { id := "IUT-I-II.example36-odd-division-polynomial-bounds"
    source :=
      "IUT I, Definition 3.1(c) torsion data; Mathlib DivisionPolynomial degree"
    status := VerificationStatus.provedKernel
    note :=
      "Proved unconditionally for the curve y^2 = x^3 - x over a field K: for " ++
        "odd n with n != 0 in K, prePsi_n has natDegree (n^2 - 1)/2, leading " ++
        "coefficient n (nonzero) and is nonzero; the root-count bound " ++
        "(prePsi_n).roots.card <= (n^2 - 1)/2 and finiteness of the root set; " ++
        "for odd n the bivariate psi_n at every solution of the curve equals " ++
        "prePsi_n(x), with the point-level form at nonsingular points.  Proved " ++
        "CONDITIONALLY: if the frozen odd group-law criterion " ++
        "(oddNsmulDivisionPolynomialCriterionCard: n • P = 0 iff psi_n(P) = 0 " ++
        "for odd n > 3) holds, then the actual n-torsion subgroup equals the " ++
        "explicit finite candidate set and is finite.  NOT proved: the " ++
        "group-law criterion for odd n > 3 (only n = 3 is proved in " ++
        "Example36DivisionTorsionThree), hence no unconditional general odd " ++
        "torsion finiteness.  No Tate module, inverse limit, theta/q-pilot or " ++
        "Anabelian claim."
    dependsOn :=
      [ "IUT-I-II.example36-division-torsion-three",
        "IUT-I-II.example36-odd-torsion-finiteness" ] }

end LeanFormal.IUT.Audit

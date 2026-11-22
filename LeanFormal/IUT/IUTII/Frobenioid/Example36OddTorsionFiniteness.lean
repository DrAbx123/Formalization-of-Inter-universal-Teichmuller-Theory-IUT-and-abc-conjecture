/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36DivisionTorsionThree
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Finiteness of the actual 3-torsion subgroup of y^2 = x^3 - x

Foundation F4c (3-torsion finiteness and odd-torsion plan).  This module proves
that the actual 3-torsion subgroup E[3] of the curve y^2 = x^3 - x is finite
over any field of characteristic different from 2, constructs the explicit
finite set of candidates on which it is concentrated, and proves that over an
algebraically closed field of characteristic zero E[3] is nontrivial.  The
exact general odd-l finiteness obligation is frozen as a card.

## Content

* y2x3xCurve_Ψ₃_ne_zero: psi_3 is a nonzero polynomial for this curve (its
  value at 0 is -1).
* y2x3xCurve_Ψ₃_roots_card_le_four: psi_3 is quartic, so its root multiset
  has at most 4 elements (Mathlib natDegree_Ψ₃_le plus card_roots').
* y2x3xCurve_quadratic_roots_card_le_two: each x-fiber y^2 = x^3 - x has at
  most two y-values (the quadratic Y^2 - (x^3 - x)).
* y2x3xCurve_y_sq_of_mem_roots, y2x3xCurve_eval_Ψ₃_of_mem_roots: membership in
  the root finsets of psi_3 and of the quadratic is converted to the
  corresponding equations.
* y2x3xCurve_equation_of_sq and y2x3xCurve_nonsingular_of_eval_Ψ₃_eq_zero: a
  solution of y^2 = x^3 - x at a root of psi_3 is a nonsingular point.
* threeTorsionCandidateIndex and threeTorsionCandidatePoint: the finite index
  type (a root x of psi_3 and a root y of Y^2 - (x^3 - x)) with its candidate
  nonsingular affine point.
* threeTorsionCandidates: the explicit finite set {0} union all candidate
  affine points.
* threeTorsionSubgroup_eq_candidates: the actual torsion subgroup, as a set,
  is exactly this finite candidate set; both inclusions use the task-72
  criterion three_nsmul_eq_zero_iff.
* threeTorsionSubgroup_finite: the actual subgroup is finite; instance
  threeTorsionSubgroupInstFinite is available over any field of
  characteristic zero.
* threeTorsionSubgroup_nontrivial: over an algebraically closed field of
  characteristic zero the actual subgroup is nontrivial, using the task-72
  nontriviality theorem exists_threeTorsionOfY2x3xCurve.

## General odd l and honest boundary

The 3-torsion finiteness proof uses the explicit quartic psi_3 and the task-72
group-law-to-division-polynomial criterion for n = 3, together with the fact
that a quadratic has at most two roots.  For general odd l the missing pieces
are exactly: (i) the group-law correspondence l • P = 0 <-> psi_l(P) = 0 for
odd l > 3 (Mathlib has psi_l and prePsi_l and degree bounds but no nsmul
correspondence for l > 3), and (ii) the nonzero/root-count bookkeeping for the
degree-(l^2-1)/2 polynomial prePsi_l in the same form used here.  These are
frozen in oddTorsionFinitenessCard; no general odd-l finiteness is claimed.
No Tate module, inverse limit, theta/q-pilot or Anabelian statement is made.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace OddTorsionFiniteness

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.DivisionTorsionThree

variable {K : Type*} [Field K]

/-! ## Roots of psi_3, root counts, and nonsingularity -/

/-- psi_3 is nonzero for the curve y^2 = x^3 - x (its value at 0 is -1). -/
theorem y2x3xCurve_Ψ₃_ne_zero :
    (y2x3xCurve (K := K)).Ψ₃ ≠ 0 := by
  intro hzero
  have h0 : (y2x3xCurve (K := K)).Ψ₃.eval 0 = -1 := by
    rw [y2x3xCurve_eval_Ψ₃]; norm_num
  rw [hzero] at h0
  simp only [Polynomial.eval_zero] at h0
  have h1 : (1 : K) = 0 := by linear_combination h0
  exact one_ne_zero h1

/-- The quartic psi_3 has at most 4 roots. -/
theorem y2x3xCurve_Ψ₃_roots_card_le_four :
    (y2x3xCurve (K := K)).Ψ₃.roots.card ≤ 4 :=
  (Polynomial.card_roots' _).trans (WeierstrassCurve.natDegree_Ψ₃_le _)

/-- For each x, the equation y^2 = x^3 - x has at most two solutions y. -/
theorem y2x3xCurve_quadratic_roots_card_le_two (c : K) :
    (Polynomial.X ^ 2 - Polynomial.C c : K[X]).roots.card ≤ 2 :=
  (Polynomial.card_roots' _).trans (by
    rw [Polynomial.natDegree_X_pow_sub_C])

/-- A solution of y^2 = x^3 - x satisfies the Weierstrass equation. -/
theorem y2x3xCurve_equation_of_sq (x y : K) (hy2 : y ^ 2 = x ^ 3 - x) :
    (y2x3xCurve (K := K)).toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [y2x3xCurve_a1, y2x3xCurve_a2, y2x3xCurve_a3, y2x3xCurve_a4, y2x3xCurve_a6]
  linear_combination hy2

/-- A solution of y^2 = x^3 - x at a root of psi_3 is a nonsingular point:
the only singular points would have y = 0, hence x in {0,1,-1}, where psi_3
takes the nonzero values -1 and -4. -/
theorem y2x3xCurve_nonsingular_of_eval_Ψ₃_eq_zero (h2 : (2 : K) ≠ 0)
    {x y : K} (hy2 : y ^ 2 = x ^ 3 - x)
    (hψ : (y2x3xCurve (K := K)).Ψ₃.eval x = 0) :
    (y2x3xCurve (K := K)).toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨y2x3xCurve_equation_of_sq x y hy2, ?_⟩
  by_cases hy0 : y = 0
  · left
    have hy : y = (y2x3xCurve (K := K)).toAffine.negY x y := by
      simp [WeierstrassCurve.Affine.negY, y2x3xCurve_a1, y2x3xCurve_a3, hy0]
    exact absurd hψ (y2x3xCurve_eval_Ψ₃_ne_zero_of_Y_eq_negY x y h2 hy2 hy)
  · right
    simp only [y2x3xCurve_a1, y2x3xCurve_a3]
    intro hneg
    apply hy0
    have h2y : (2 : K) * y = 0 := by linear_combination hneg
    exact (mul_eq_zero.mp h2y).resolve_left h2

section DecidableEq

variable [DecidableEq K]

/-- A root of psi_3 in the root finset evaluates to zero. -/
theorem y2x3xCurve_eval_Ψ₃_of_mem_roots {x : K}
    (hx : x ∈ (y2x3xCurve (K := K)).Ψ₃.roots.toFinset) :
    (y2x3xCurve (K := K)).Ψ₃.eval x = 0 := by
  rw [Multiset.mem_toFinset,
    Polynomial.mem_roots (y2x3xCurve_Ψ₃_ne_zero (K := K))] at hx
  exact hx

/-- A root of Y^2 - (x^3 - x) in the root finset satisfies y^2 = x^3 - x. -/
theorem y2x3xCurve_y_sq_of_mem_roots {x y : K}
    (hy : y ∈ (Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) : K[X]).roots.toFinset) :
    y ^ 2 = x ^ 3 - x := by
  have hne : (Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) : K[X]) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 2) (x ^ 3 - x)
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hne] at hy
  have h : y ^ 2 - (x ^ 3 - x) = 0 := by
    simpa [Polynomial.IsRoot] using hy
  linear_combination h

/-! ## The finite candidate set and its equality with the torsion subgroup -/

/-- The finite index set: a root x of psi_3 together with a root y of the
quadratic Y^2 - (x^3 - x). -/
noncomputable abbrev threeTorsionCandidateIndex (K : Type*) [Field K] [DecidableEq K] :
    Type _ :=
  Σ x : {x : K // x ∈ (y2x3xCurve (K := K)).Ψ₃.roots.toFinset},
    {y : K // y ∈
      (Polynomial.X ^ 2 - Polynomial.C (x.1 ^ 3 - x.1) : K[X]).roots.toFinset}

/-- The candidate nonsingular affine point attached to a pair (x, y) of roots. -/
noncomputable def threeTorsionCandidatePoint (h2 : (2 : K) ≠ 0) :
    threeTorsionCandidateIndex K → (y2x3xCurve (K := K)).toAffine.Point :=
  fun p =>
    WeierstrassCurve.Affine.Point.some p.1.1 p.2.1
      (y2x3xCurve_nonsingular_of_eval_Ψ₃_eq_zero h2
        (y2x3xCurve_y_sq_of_mem_roots p.2.2)
        (y2x3xCurve_eval_Ψ₃_of_mem_roots p.1.2))

/-- The explicit finite set of candidates for E[3]: the point at infinity and
all candidate affine points (x, y) with psi_3(x) = 0 and y^2 = x^3 - x. -/
noncomputable def threeTorsionCandidates (h2 : (2 : K) ≠ 0) :
    Finset ((y2x3xCurve (K := K)).toAffine.Point) :=
  insert 0 (Finset.univ.image (threeTorsionCandidatePoint (K := K) h2))

/-- Every candidate point is an actual 3-torsion point. -/
theorem threeTorsionCandidatePoint_mem (h2 : (2 : K) ≠ 0)
    (p : threeTorsionCandidateIndex K) :
    threeTorsionCandidatePoint (K := K) h2 p ∈ threeTorsionSubgroup K := by
  rw [threeTorsionSubgroup_mem_iff_eval K h2]
  simp only [threeTorsionCandidatePoint]
  cases p with
  | mk x y =>
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      (y2x3xCurve (K := K)).evalDivisionPolynomial_eq_eval_preΨ_of_odd
        ((y2x3xCurve_nonsingular_of_eval_Ψ₃_eq_zero h2
          (y2x3xCurve_y_sq_of_mem_roots y.2)
          (y2x3xCurve_eval_Ψ₃_of_mem_roots x.2)).1)
        (by decide : ¬ Even (3 : ℤ)),
      (y2x3xCurve (K := K)).preΨ_three]
    exact y2x3xCurve_eval_Ψ₃_of_mem_roots x.2

/-- **The actual torsion subgroup equals the explicit finite candidate set.** -/
theorem threeTorsionSubgroup_eq_candidates (h2 : (2 : K) ≠ 0) :
    (threeTorsionSubgroup K : Set ((y2x3xCurve (K := K)).toAffine.Point)) =
      ↑(threeTorsionCandidates (K := K) h2) := by
  ext P
  constructor
  · intro hP
    have hP' : (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint 3 P = 0 :=
      (threeTorsionSubgroup_mem_iff_eval K h2 P).mp hP
    rw [Finset.mem_coe]
    cases P with
    | zero =>
      rw [threeTorsionCandidates, Finset.mem_insert]
      exact Or.inl rfl
    | some x y hns =>
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        (y2x3xCurve (K := K)).evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1
          (by decide : ¬ Even (3 : ℤ)),
        (y2x3xCurve (K := K)).preΨ_three] at hP'
      have hxmem : x ∈ (y2x3xCurve (K := K)).Ψ₃.roots.toFinset := by
        rw [Multiset.mem_toFinset,
          Polynomial.mem_roots (y2x3xCurve_Ψ₃_ne_zero (K := K))]
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
      rw [threeTorsionCandidates, Finset.mem_insert, Finset.mem_image]
      right
      refine ⟨⟨⟨x, hxmem⟩, ⟨y, hymem⟩⟩, Finset.mem_univ _, ?_⟩
      simp only [threeTorsionCandidatePoint]
  · intro hP
    rw [Finset.mem_coe, threeTorsionCandidates, Finset.mem_insert,
      Finset.mem_image] at hP
    rcases hP with rfl | ⟨p, _, hp⟩
    · exact (threeTorsionSubgroup_mem_iff_eval K h2 0).mpr rfl
    · rw [← hp]
      exact threeTorsionCandidatePoint_mem h2 p

/-! ## Finiteness, the finite instance, and nontriviality -/

/-- The actual 3-torsion subgroup is finite over any field with 2 != 0. -/
theorem threeTorsionSubgroup_finite (h2 : (2 : K) ≠ 0) :
    Finite (threeTorsionSubgroup K) := by
  have hfin : ((threeTorsionSubgroup K : Set
      ((y2x3xCurve (K := K)).toAffine.Point))).Finite := by
    rw [threeTorsionSubgroup_eq_candidates (K := K) h2]
    exact (threeTorsionCandidates (K := K) h2).finite_toSet
  exact hfin.to_subtype

/-- Over a field of characteristic zero the actual 3-torsion subgroup is
finite. -/
noncomputable instance threeTorsionSubgroupInstFinite [CharZero K] :
    Finite (threeTorsionSubgroup K) :=
  threeTorsionSubgroup_finite (by norm_num : (2 : K) ≠ 0)

/-- Over an algebraically closed field of characteristic zero the actual
3-torsion subgroup is nontrivial. -/
theorem threeTorsionSubgroup_nontrivial [IsAlgClosed K] [CharZero K] :
    Nontrivial (threeTorsionSubgroup K) := by
  obtain ⟨P, h3, hPne⟩ := exists_threeTorsionOfY2x3xCurve K
  exact ⟨⟨P, (threeTorsionSubgroup_mem_iff K P).mpr h3⟩, 0, fun heq =>
    hPne (Subtype.ext_iff.mp heq)⟩

/-- Over an algebraically closed field of characteristic zero the actual
3-torsion subgroup carries a nontriviality instance. -/
noncomputable instance threeTorsionSubgroupInstNontrivial [IsAlgClosed K] [CharZero K] :
    Nontrivial (threeTorsionSubgroup K) :=
  threeTorsionSubgroup_nontrivial

/-! ## Frozen card: general odd-l torsion finiteness -/

/-- **Frozen card: general odd-l torsion finiteness.**  For every odd l > 3
and every field K with 2 != 0, the l-torsion subgroup is finite and is
characterized by the vanishing of psi_l.  The two missing inputs are exactly:
(i) the group-law-to-division-polynomial bridge l • P = 0 <-> psi_l(P) = 0 for
odd l > 3, and (ii) the nonzero/root-count bookkeeping for prePsi_l (degree
(l^2-1)/2) in the form used for l = 3 in this file.  This is a card, not a
theorem, and it is not consumed. -/
def oddTorsionFinitenessCard : Prop :=
  ∀ (K : Type*) [Field K] [DecidableEq K], (2 : K) ≠ 0 →
    ∀ l : ℕ, Odd l → 3 < l →
      (∀ P : (y2x3xCurve (K := K)).toAffine.Point,
        (l : ℕ) • P = 0 ↔
          (y2x3xCurve (K := K)).evalDivisionPolynomialAtPoint (l : ℤ) P = 0) ∧
        Finite (AddSubgroup.torsionBy
          (y2x3xCurve (K := K)).toAffine.Point (l : ℤ))

end DecidableEq

end OddTorsionFiniteness
end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- Audit record for Foundation F4c: finiteness and nontriviality of the actual
3-torsion subgroup, and the frozen general odd-l obligation. -/
def example36OddTorsionFiniteness : Obligation :=
  { id := "IUT-I-II.example36-odd-torsion-finiteness"
    source :=
      "IUT I, Definition 3.1(c) torsion data; Mathlib division polynomial degree"
    status := VerificationStatus.provedKernel
    note :=
      "Proved: psi_3 is nonzero and has at most 4 roots for y^2 = x^3 - x " ++
        "(Mathlib natDegree_Ψ₃_le and card_roots'); each equation y^2 = x^3 - x " ++
        "has at most two solutions y (quadratic root count); every 3-torsion " ++
        "point is a candidate (the point at infinity, or an affine nonsingular " ++
        "(x,y) with psi_3(x)=0 and y^2 = x^3 - x, by the task-72 criterion); the " ++
        "actual subgroup AddSubgroup.torsionBy _ 3 equals the explicit finite " ++
        "candidate Finset (threeTorsionSubgroup_eq_candidates); hence E[3] is " ++
        "finite over any field with 2 != 0 (threeTorsionSubgroup_finite), with " ++
        "a Finite instance over characteristic-zero fields; over algebraically " ++
        "closed characteristic-zero fields the actual subgroup is nontrivial " ++
        "(threeTorsionSubgroup_nontrivial, using the task-72 root/square-root " ++
        "construction).  MISSING (frozen card oddTorsionFinitenessCard): general " ++
        "odd-l finiteness, exactly the group-law-to-division-polynomial bridge " ++
        "l • P = 0 <-> psi_l(P) = 0 for odd l > 3 and the nonzero/root-count " ++
        "bookkeeping for prePsi_l.  No Tate module, inverse limit, theta/q-pilot " ++
        "or Anabelian claim."
    dependsOn :=
      [ "IUT-I-II.example36-division-torsion-three",
        "Foundations.Geometry.elliptic-torsion-galois" ] }

end LeanFormal.IUT.Audit

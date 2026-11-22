/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/
import tmp.sheaf.xif.paper.S1362PrePsiSeparabilityActual
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# S1405: the exact torsion-cardinality conclusions of Tau Ceti, in Mathlib v4.32.2

Tau Ceti (tmp/TauCeti, commit ff33d5f0811d2ec351fc04ab46c34d1bff53df8a,
Lean v4.36.0-rc1) proves:

* TauCeti.Isogeny.card_zsmul_fiber: over an algebraically closed field,
  for (n : F) != 0, a nonempty [n]-fibre has exactly n.natAbs ^ 2
  points;
* WeierstrassCurve.Affine.natCard_torsionBy_of_torsion_rational: when the
  geometric n-torsion is rational and (n : F) != 0, Mathlib's intrinsic
  torsion subgroup AddSubgroup.torsionBy has exactly n.natAbs ^ 2
  elements.

This file ports **only those exact cardinality conclusions**.  It does not
vendor Tau Ceti's isogeny/separability closure: the deep input used by Tau
Ceti, the equality #ker [n] = n ^ 2, is isolated below, and the exact
conclusions are proved from it by purely group-theoretic arguments.

## What is actually proved here

1. natCard_zsmul_fiber_eq_natCard_torsionBy: a nonempty fibre of n • ·
   has the cardinality of the n-torsion subgroup.  This is the whole
   combinatorial content of the fibre count.
2. natCard_torsionBy_eq_of_forall_mem_range: if every geometric
   n-torsion point lies in the range of a base change, the base-field
   torsion subgroup has the same cardinality as the geometric one.
3. card_zsmul_fiber_eq_sq_of_natCard_torsionBy and
   natCard_torsionBy_of_torsion_rational_of_geometric are the exact source
   conclusions, with the single missing geometric count as an explicit
   hypothesis.
4. The current tree supplies exactly the two ingredients that Tau Ceti's
   isogeny theory supplies:
   * s1329DivisionCriterion (the group-law criterion
     l • P = 0 <-> ψ_l(P) = 0, frozen in
     S1329RankTwoTorsionBasisActual);
   * separability / the full root count of the odd division polynomial
     (S1362PrePsiSeparabilityActual).
   Under these two inputs we prove
   natCard_torsionBy_eq_sq_of_criterion_and_separable for every elliptic
   curve over an algebraically closed field of characteristic not two, for
   odd l; this discharges the geometric count in (3) and therefore gives
   the exact conclusions natCard_torsionBy_of_torsion_rational_of_criterion_and_separable
   and card_zsmul_fiber_of_criterion_and_separable.
5. The concrete Gaussian curve of the tree is instantiated:
   s1405Gaussian_natCard_torsionBy, s1405Gaussian_card_zsmul_fiber, and
   s1405Gaussian_s1298_natCard (the S1298 carrier count) follow from
   the frozen S1329 criterion and S1362 root count.

## The exact remaining field

For the **unconditional** source statements in the current tree, the exact
first field is the geometric n ^ 2 torsion count over the algebraic
closure, i.e. Tau Ceti's
card_ker_mulByIntIsogeny_of_torsion_rational / card_zsmul_fiber itself.
Equivalently, in the current tree it is the pair

* s1329DivisionCriterion W n (group law <-> division polynomial), and
* (W.preΨ n).Separable (full distinct-root count).

No sorry, new axiom, True/PUnit substitute, or arbitrary data is used.
EllipticPrimeTorsionCardinality supplies only the upper bound on the
division locus, not this equality; the exact equality needs the criterion and
separability, which is why the tree files above are used instead.

## Port notes

The rationality theorems carry one classical instance argument
[DecidableEq (AlgebraicClosure W.FunctionField)], required by Mathlib's
Point.baseChange; it is not a mathematical hypothesis.  The odd-natAbs
theorems additionally assume 2 != 0 in the base field, as the current-tree
odd division-polynomial route does.  The source's general integer n is
covered by the geometric-count statements; the odd case is discharged by
the current-tree criterion and separability.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009],
  III.6.4(b).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1405TorsionCardinalityPortActual

open WeierstrassCurve
open WeierstrassCurve.Affine
open scoped WeierstrassCurve
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual
open LeanFormal.IUT.XiFPaper.S1362PrePsiSeparabilityActual

/-! ## 1. The group-theoretic core -/

/-- **A nonempty fibre of n • · has the cardinality of the n-torsion
subgroup.**  Translation by P₀ identifies {P | n • P = T} with
{Q | n • Q = 0}, and the latter is AddSubgroup.torsionBy A n by
definition. -/
theorem natCard_zsmul_fiber_eq_natCard_torsionBy {A : Type*} [AddCommGroup A]
    (n : ℤ) {T P₀ : A} (hP₀ : n • P₀ = T) :
    Nat.card {P : A // n • P = T} = Nat.card (AddSubgroup.torsionBy A n) := by
  classical
  have key : Nat.card {P : A // n • P = T} = Nat.card {Q : A // n • Q = 0} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun P => ⟨P.1 - P₀, ?_⟩
        invFun := fun Q => ⟨Q.1 + P₀, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · show n • (P.1 - P₀) = 0
      rw [zsmul_sub, P.2, hP₀, sub_self]
    · show n • (Q.1 + P₀) = T
      rw [zsmul_add, Q.2, hP₀, zero_add]
    · intro P
      apply Subtype.ext
      simp
    · intro Q
      apply Subtype.ext
      simp
  rw [key]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

/-- **Rationality transfers the torsion count.**  If every geometric
n-torsion point lies in the range of an injective hom f, then the
n-torsion subgroups on both sides have the same cardinality. -/
theorem natCard_torsionBy_eq_of_forall_mem_range
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (n : ℤ)
    (hf : Function.Injective f)
    (hrat : ∀ Q : B, n • Q = 0 → Q ∈ Set.range f) :
    Nat.card (AddSubgroup.torsionBy A n) = Nat.card (AddSubgroup.torsionBy B n) := by
  classical
  refine Nat.card_congr (Equiv.ofBijective
    (fun P : AddSubgroup.torsionBy A n =>
      (⟨f P, ?_⟩ : AddSubgroup.torsionBy B n)) ?_)
  · change n • f (P : A) = 0
    rw [← map_zsmul]
    rw [show n • (P : A) = 0 from P.2, map_zero]
  · constructor
    · intro P Q h
      apply Subtype.ext
      exact hf (congrArg (fun R : AddSubgroup.torsionBy B n => (R : B)) h)
    · intro Q
      obtain ⟨P, hP⟩ := hrat Q Q.2
      have hPtor : n • P = 0 := by
        apply hf
        rw [map_zsmul, hP, map_zero]
        exact Q.2
      exact ⟨⟨P, hPtor⟩, Subtype.ext hP⟩

/-! ## 2. The exact source conclusions from the single geometric input -/

/-- **Exact fibre cardinality from the exact torsion cardinality.**  This is
the conclusion of Tau Ceti's card_zsmul_fiber, with the deep geometric
count hcard exposed as the one input. -/
theorem card_zsmul_fiber_eq_sq_of_natCard_torsionBy {A : Type*} [AddCommGroup A]
    {n : ℤ} (hcard : Nat.card (AddSubgroup.torsionBy A n) = n.natAbs ^ 2)
    {T P₀ : A} (hP₀ : n • P₀ = T) :
    Nat.card {P : A // n • P = T} = n.natAbs ^ 2 := by
  rw [natCard_zsmul_fiber_eq_natCard_torsionBy (n := n) hP₀, hcard]

section GeneralCurve

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **Exact torsion cardinality under rationality**, the conclusion of Tau
Ceti's natCard_torsionBy_of_torsion_rational, with Tau Ceti's geometric
count supplied as hgeom.

hgeom is exactly the content of Tau Ceti's
card_ker_mulByIntIsogeny_of_torsion_rational; no isogeny or separable-degree
theory is imported or vendored. -/
theorem natCard_torsionBy_of_torsion_rational_of_geometric
    [DecidableEq (AlgebraicClosure W.FunctionField)] {n : ℤ}
    (hchar : (n : F) ≠ 0)
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).Point,
      n • P = 0 →
        P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)))
    (hgeom : Nat.card
      (AddSubgroup.torsionBy (W.baseChange (AlgebraicClosure W.FunctionField)).Point n) =
        n.natAbs ^ 2) :
    Nat.card (AddSubgroup.torsionBy (W.baseChange F).Point n) = n.natAbs ^ 2 := by
  classical
  have hf : Function.Injective
      (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)) :=
    Point.map_injective (W' := W)
      (f := Algebra.ofId F (AlgebraicClosure W.FunctionField))
  have h := natCard_torsionBy_eq_of_forall_mem_range
    (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)) n hf hrat
  exact h.trans hgeom

end GeneralCurve

/-! ## 3. The current-tree replacement: the group-law criterion and
separability of the odd division polynomial -/

/-- The natural absolute value of an integer, cast to a field, is nonzero as
soon as the integer itself is. -/
theorem natAbs_cast_ne_zero {F : Type*} [Field F] {n : ℤ} (h : (n : F) ≠ 0) :
    (n.natAbs : F) ≠ 0 := by
  have hcal : ((n.natAbs : ℤ) : F) = (n : F) ∨
      ((n.natAbs : ℤ) : F) = -(n : F) := by
    rcases Int.natAbs_eq n with h1 | h1
    · left
      conv_rhs => rw [h1]
    · right
      conv_rhs => rw [h1]
      push_cast
      ring
  have h' : ((n.natAbs : ℤ) : F) ≠ 0 := by
    rcases hcal with hcal | hcal
    · rwa [hcal]
    · rw [hcal]
      exact neg_ne_zero.mpr h
  simpa using h'

section Criterion

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

/-- **No root of preΨ_l is a 2-torsion x-coordinate**, for odd l over
an algebraically closed field of characteristic not two, assuming the
group-law criterion.

This is the general form of
S1329RankTwoTorsionBasisActual.s1329NoTwoTorsionRoots_of_criterion: over a
root x of preΨ_l the Weierstrass equation has the point
y₀ = -(a₁x + a₃)/2; the criterion makes it l-torsion, while the 2-torsion
criterion makes it 2-torsion; coprimality of 2 and odd l forces it to be
zero, contradicting Point.some_ne_zero. -/
theorem noTwoTorsionRoots_of_criterion {l : ℕ} (hl : Odd l) (h2 : (2 : K) ≠ 0)
    (hcrit : s1329DivisionCriterion W l) (hpre : W.preΨ (l : ℤ) ≠ 0) :
    ∀ x ∈ s1329RootFinset W l, (W.Ψ₂Sq).eval x ≠ 0 := by
  classical
  intro x hx hc
  have hodd : ¬ Even (l : ℤ) := by
    rw [Int.even_coe_nat, Nat.not_even_iff_odd]
    exact hl
  set y0 : K := (-(W.a₁ * x + W.a₃)) / 2 with hy0
  have hy0eq : 2 * y0 + W.a₁ * x + W.a₃ = 0 := by
    rw [hy0]
    field_simp
    ring
  have hEq : W.Equation x y0 :=
    (s1329Equation_iff_sq W h2 x y0).mpr (by rw [hy0eq, hc]; ring)
  have hns : W.Nonsingular x y0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hEq
  have hψl : (W.preΨ (l : ℤ)).eval x = 0 :=
    s1329PreΨ_eval_of_mem_roots W hpre hx
  have hltor : (l : ℤ) • WeierstrassCurve.Affine.Point.some x y0 hns = 0 := by
    rw [hcrit]
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hodd]
    exact hψl
  have htwo : (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y0 hns = 0 := by
    refine (W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero _).mpr ?_
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      WeierstrassCurve.evalDivisionPolynomial_two]
    exact hy0eq
  have hltor' : l • WeierstrassCurve.Affine.Point.some x y0 hns = 0 := by
    simpa [natCast_zsmul] using hltor
  have hdvd2 : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) ∣ 2 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
  have hdvdl : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) ∣ l :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hltor'
  have hcop : Nat.Coprime 2 l := Nat.coprime_two_left.mpr hl
  have hone : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) = 1 := by
    have hgcd : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) ∣ Nat.gcd 2 l :=
      Nat.dvd_gcd hdvd2 hdvdl
    rw [hcop] at hgcd
    exact Nat.dvd_one.mp hgcd
  exact WeierstrassCurve.Affine.Point.some_ne_zero hns
    (AddMonoid.addOrderOf_eq_one_iff.mp hone)

/-- **The exact l-torsion cardinality from the current-tree inputs**, for
odd l over an algebraically closed field of characteristic not two.

The two hypotheses are exactly the two frozen inputs of
S1329RankTwoTorsionBasisActual / S1362PrePsiSeparabilityActual:

* hcrit: the group-law criterion l • P = 0 <-> ψ_l(P) = 0;
* hsep: separability of preΨ_l, equivalently the full distinct-root
  count (l ^ 2 - 1) / 2.

Under them the division locus has 1 + 2 * ((l ^ 2 - 1) / 2) = l ^ 2 points,
which is the geometric count Tau Ceti obtains from its isogeny theory. -/
theorem natCard_torsionBy_eq_sq_of_criterion_and_separable {l : ℕ}
    (hl : Odd l) (h2 : (2 : K) ≠ 0) (hlK : (l : K) ≠ 0)
    (hcrit : s1329DivisionCriterion W l)
    (hsep : (W.preΨ (l : ℤ)).Separable) :
    Nat.card (AddSubgroup.torsionBy W.Point (l : ℤ)) = l ^ 2 := by
  classical
  have hpre : W.preΨ (l : ℤ) ≠ 0 :=
    WeierstrassCurve.preΨ_ne_zero W (by simpa using hlK)
  have hodd : ¬ Even (l : ℤ) := by
    rw [Int.even_coe_nat, Nat.not_even_iff_odd]
    exact hl
  have hsplit : (W.preΨ (l : ℤ)).Splits := IsAlgClosed.splits _
  have hnodup : (W.preΨ (l : ℤ)).roots.Nodup :=
    (Polynomial.nodup_roots_iff_of_splits hpre hsplit).mpr hsep
  have hcard : (W.preΨ (l : ℤ)).roots.toFinset.card = (l ^ 2 - 1) / 2 := by
    rw [Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots]
    rw [WeierstrassCurve.natDegree_preΨ W (by simpa using hlK)]
    rw [if_neg hodd, Int.natAbs_natCast]
  have hΨ := noTwoTorsionRoots_of_criterion W hl h2 hcrit hpre
  exact (s1329NatCard_eq_sq_iff_separable W l h2 hcrit hodd hpre hΨ hl).mpr hcard

/-- The integer form of natCard_torsionBy_eq_sq_of_criterion_and_separable:
the count is read at n.natAbs, and n • P = 0 <-> n.natAbs • P = 0 because
n = ± n.natAbs. -/
theorem natCard_torsionBy_eq_sq_of_criterion_and_separable_int {n : ℤ}
    (hnodd : Odd n.natAbs) (h2 : (2 : K) ≠ 0) (hnK : (n : K) ≠ 0)
    (hcrit : s1329DivisionCriterion W n.natAbs)
    (hsep : (W.preΨ (n.natAbs : ℤ)).Separable) :
    Nat.card (AddSubgroup.torsionBy W.Point n) = n.natAbs ^ 2 := by
  have hmem : AddSubgroup.torsionBy W.Point n =
      AddSubgroup.torsionBy W.Point (n.natAbs : ℤ) := by
    ext P
    show n • P = 0 ↔ (n.natAbs : ℤ) • P = 0
    rcases Int.natAbs_eq n with h | h
    · conv_lhs => rw [h]
    · conv_lhs => rw [h]
      rw [neg_zsmul, neg_eq_zero]
  rw [hmem]
  exact natCard_torsionBy_eq_sq_of_criterion_and_separable W hnodd h2
    (natAbs_cast_ne_zero hnK) hcrit hsep

end Criterion

/-! ## 4. The source conclusions with the current-tree replacement -/

section Rational

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **Tau Ceti's natCard_torsionBy_of_torsion_rational with the deep
isogeny input replaced by the current-tree criterion and separability.**

The hypotheses are the source's hchar and rationality hrat, together with:

* characteristic not two (h2F), needed by the tree's division-polynomial
  and two-torsion arguments;
* oddness of n.natAbs (hnodd), since the tree route counts odd division
  polynomials (S1329);
* the group-law criterion and separability for the base change to
  AlgebraicClosure W.FunctionField, i.e. the exact two frozen gaps of the
  current tree.

This is the exact source conclusion in the current API.  No isogeny theory,
separable degree, or Tau Ceti module is imported. -/
theorem natCard_torsionBy_of_torsion_rational_of_criterion_and_separable
    [DecidableEq (AlgebraicClosure W.FunctionField)]
    {n : ℤ} (hchar : (n : F) ≠ 0) (h2F : (2 : F) ≠ 0)
    (hnodd : Odd n.natAbs)
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).Point,
      n • P = 0 →
        P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)))
    (hcrit : s1329DivisionCriterion
      (W.baseChange (AlgebraicClosure W.FunctionField)) n.natAbs)
    (hsep : ((W.baseChange (AlgebraicClosure W.FunctionField)).preΨ
      (n.natAbs : ℤ)).Separable) :
    Nat.card (AddSubgroup.torsionBy (W.baseChange F).Point n) = n.natAbs ^ 2 := by
  classical
  have hΩn : (n : AlgebraicClosure W.FunctionField) ≠ 0 := by
    rw [← map_intCast (algebraMap F (AlgebraicClosure W.FunctionField)) n]
    exact (map_ne_zero (algebraMap F (AlgebraicClosure W.FunctionField))).mpr hchar
  have h2Ω : (2 : AlgebraicClosure W.FunctionField) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (AlgebraicClosure W.FunctionField)) 2]
    exact (map_ne_zero (algebraMap F (AlgebraicClosure W.FunctionField))).mpr h2F
  haveI : (W.baseChange (AlgebraicClosure W.FunctionField)).IsElliptic := by
    change (W.map (algebraMap F (AlgebraicClosure W.FunctionField))).IsElliptic
    infer_instance
  apply natCard_torsionBy_of_torsion_rational_of_geometric W hchar hrat
  exact natCard_torsionBy_eq_sq_of_criterion_and_separable_int
    (W.baseChange (AlgebraicClosure W.FunctionField)) hnodd h2Ω hΩn hcrit hsep

/-- **Tau Ceti's card_zsmul_fiber with the deep isogeny input replaced by
the current-tree criterion and separability**, over an algebraically closed
field of characteristic not two and for odd n.natAbs. -/
theorem card_zsmul_fiber_of_criterion_and_separable [IsAlgClosed F]
    {n : ℤ} (hchar : (n : F) ≠ 0) (h2F : (2 : F) ≠ 0)
    (hnodd : Odd n.natAbs)
    (hcrit : s1329DivisionCriterion (W.baseChange F) n.natAbs)
    (hsep : ((W.baseChange F).preΨ (n.natAbs : ℤ)).Separable)
    {T P₀ : (W.baseChange F).Point} (hP₀ : n • P₀ = T) :
    Nat.card {P : (W.baseChange F).Point // n • P = T} = n.natAbs ^ 2 := by
  haveI : (W.baseChange F).IsElliptic := by
    change (W.map (algebraMap F F)).IsElliptic
    infer_instance
  exact card_zsmul_fiber_eq_sq_of_natCard_torsionBy
    (natCard_torsionBy_eq_sq_of_criterion_and_separable_int (W.baseChange F)
      hnodd h2F hchar hcrit hsep) hP₀

end Rational

/-! ## 5. The concrete Gaussian curve -/

section Gaussian

local instance s1405GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1405ClosureDecEq (l : PrimeGeFive) :
    DecidableEq (S1329Closure l) :=
  Classical.decEq _

/-- l is odd: it is a prime at least five. -/
theorem s1405Odd (l : PrimeGeFive) : Odd l.value :=
  l.prime.odd_of_ne_two (by have := l.ge_five; omega)

/-- **The exact l-torsion cardinality of the Gaussian curve**, from the
frozen S1329 criterion and the S1362 root count. -/
theorem s1405Gaussian_natCard_torsionBy (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) (hroot : S1362RootCount l) :
    Nat.card (AddSubgroup.torsionBy (S1329Curve l).Point (l.value : ℤ)) =
      l.value ^ 2 := by
  have hsep : ((S1329Curve l).preΨ (l.value : ℤ)).Separable :=
    (s1362RootCount_iff_separable l).mp hroot
  exact natCard_torsionBy_eq_sq_of_criterion_and_separable (S1329Curve l)
    (s1405Odd l) (s1329Concrete_two_ne_zero l) (s1329Concrete_l_ne_zero l)
    hcrit hsep

/-- **The exact [l]-fibre cardinality of the Gaussian curve**, the
conclusion of Tau Ceti's card_zsmul_fiber for this curve. -/
theorem s1405Gaussian_card_zsmul_fiber (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) (hroot : S1362RootCount l)
    {T P₀ : (S1329Curve l).Point} (hP₀ : (l.value : ℤ) • P₀ = T) :
    Nat.card {P : (S1329Curve l).Point // (l.value : ℤ) • P = T} =
      l.value ^ 2 :=
  card_zsmul_fiber_eq_sq_of_natCard_torsionBy
    (s1405Gaussian_natCard_torsionBy l hcrit hroot) hP₀

/-- **The S1298 torsion-carrier cardinality** is the same exact count:
the projective carrier is additively equivalent to the affine torsion
subgroup (s1329NatCard_carrier_eq). -/
theorem s1405Gaussian_s1298_natCard (l : PrimeGeFive)
    (hcrit : S1329ConcreteCriterion l) (hroot : S1362RootCount l) :
    Nat.card (S1298TorsionCarrier l) = l.value ^ 2 := by
  rw [s1329NatCard_carrier_eq]
  exact s1405Gaussian_natCard_torsionBy l hcrit hroot

end Gaussian

/-! ## 6. Axiom footprint of the ported conclusions -/

#print axioms natCard_zsmul_fiber_eq_natCard_torsionBy
#print axioms natCard_torsionBy_eq_of_forall_mem_range
#print axioms card_zsmul_fiber_eq_sq_of_natCard_torsionBy
#print axioms natCard_torsionBy_of_torsion_rational_of_geometric
#print axioms natCard_torsionBy_eq_sq_of_criterion_and_separable
#print axioms natCard_torsionBy_of_torsion_rational_of_criterion_and_separable
#print axioms card_zsmul_fiber_of_criterion_and_separable
#print axioms s1405Gaussian_natCard_torsionBy
#print axioms s1405Gaussian_card_zsmul_fiber
#print axioms s1405Gaussian_s1298_natCard

end LeanFormal.IUT.XiFPaper.S1405TorsionCardinalityPortActual
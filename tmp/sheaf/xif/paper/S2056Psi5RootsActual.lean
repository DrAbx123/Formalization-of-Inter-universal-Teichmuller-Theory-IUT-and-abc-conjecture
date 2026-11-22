/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
-/
import tmp.sheaf.xif.paper.S1982D5FiveActual
import tmp.sheaf.xif.paper.S1924ZeroCriterionActual
import tmp.sheaf.xif.paper.S1467FunctionFieldPullbackActual

/-!
# S2056: the twelve roots of prePsi_5 and the twelve pairs {+-P}, Galois-equivariantly

D5(1) of the S1987 report asks for the Galois-equivariant bijection between the
twelve roots of the odd 5-division polynomial prePsi_5 and the twelve pairs
{+-P} of nonzero 5-torsion points of the actual curve E' = S1720Curve over the
actual number field F' = S1720Field, base changed to an algebraic closure K.

## Main result

S2056RootPairEquiv : S2056Root ~= S2056Pair is a bijection between

* S2056Root, the twelve distinct roots of prePsi_5 (cardinality 12 from
  S1982RootCount_five), and
* S2056Pair, the two-element negation-closed subsets of the nonzero 5-torsion
  E'(K)[5] minus {0}, i.e. the twelve pairs {P, -P}.

The map is the canonical x |-> {P : 5P = 0, P != 0, x(P) = x}: it uses the
x-coordinate and never a choice of sign, so it commutes with every
F'-automorphism of K (S2056RootToPair_equivariant).

## Proof route

* S1924S1906Criterion (the group-law criterion 5 • P = 0 <-> psi_5(P) = 0,
  proved in S1924 from the universal multiplication-by-n formula) turns
  torsion into zeros of the division polynomial and back; Mathlib's
  evalDivisionPolynomial_eq_eval_prePsi_of_odd removes the y-coordinate.
* Nonemptiness of the fibre at a root (S2056Fibre_nonempty) is the classical
  square-root construction of a point over a root of the fibre quadratic
  (s1329Equation_iff_sq), using that no root of prePsi_5 is a 2-torsion
  x-coordinate (S1906NoTwoTorsionRoots_of_criterion).
* The fibre is finite of cardinality two: it is closed under negation
  (S2056Fibre_neg_mem), contains P and -P which are distinct because a
  nonzero 5-torsion point cannot be 2-torsion (S2056_ne_neg), and two points
  with the same x-coordinate differ by a sign (Mathlib's X_eq_iff).
* Surjectivity uses the converse direction: a nonzero 5-torsion point has
  x-coordinate a root of prePsi_5 (S2056_xCoord_mem_rootFinset_of_torsion).

No sorry, no admit, no axiom, no opaque, no native_decide.  All constants
below are kernel-checked; the axiom footprint is printed at the end.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1924ZeroCriterionActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual

namespace LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual

/-! ## 1. The l = 5 carriers -/

/-- The algebraic closure K of F' used throughout. -/
abbrev S2056K : Type := S1906K

/-- Classical decidable equality on K.  This is needed by Mathlib's affine group
law on W.Point: Mathlib's AddCommGroup W.Point instance lives in the
[DecidableEq F] section. -/
instance S2056KDecEq : DecidableEq S2056K := Classical.decEq _

/-- The actual curve E' base changed to K. -/
abbrev S2056W : WeierstrassCurve.Affine S2056K := S1906W

/-- E' over K is elliptic. -/
instance S2056W_isElliptic : S2056W.IsElliptic := S1982W_isElliptic

/-- The 5-torsion subgroup of E'(K). -/
abbrev S2056Torsion : Type := AddSubgroup.torsionBy S2056W.Point (5 : Int)

/-- The nonzero 5-torsion points. -/
abbrev S2056NonzeroTorsion : Type := {P : S2056Torsion // (P.1 : S2056W.Point) ≠ 0}

/-- The distinct roots of prePsi_5 in K. -/
abbrev S2056RootFinset : Finset S2056K := (S2056W.preΨ (5 : Int)).roots.toFinset

/-- The root set of prePsi_5. -/
abbrev S2056Root : Type := {x : S2056K // x ∈ S2056RootFinset}

/-- Negation on the nonzero 5-torsion. -/
instance S2056NonzeroTorsion_neg : Neg S2056NonzeroTorsion where
  neg P := ⟨-P.1, by
    intro h
    have h' : (P.1 : S2056W.Point) = 0 := by
      simpa using neg_eq_zero.mp h
    exact P.2 h'⟩

/-- A pair {+-P} of nonzero 5-torsion points: a two-element negation-closed
finite set. -/
abbrev S2056Pair : Type :=
  {S : Finset S2056NonzeroTorsion // S.card = 2 ∧ ∀ P ∈ S, -P ∈ S}

/-! ## 2. Cardinalities -/

/-- The affine 5-torsion has 25 elements (S1982). -/
theorem S2056Torsion_card : Nat.card S2056Torsion = 25 := by
  have h := S1982NatCard_LTorsion_five
  have h' := S1906NatCard_LTorsion_eq_affine S1982Five
  simpa [S2056Torsion, S2056W, S1982Five] using h'.symm.trans h

/-- The affine 5-torsion is finite. -/
instance S2056Torsion_finite : Finite S2056Torsion := by
  classical
  by_contra hfin
  haveI : Infinite S2056Torsion := not_finite_iff_infinite.mp hfin
  have hcard := S2056Torsion_card
  rw [Nat.card_eq_zero_of_infinite] at hcard
  norm_num at hcard

/-- Fintype instance for the 5-torsion. -/
instance S2056Torsion_fintype : Fintype S2056Torsion := Fintype.ofFinite _

/-- Fintype instance for the nonzero 5-torsion. -/
instance S2056NonzeroTorsion_fintype : Fintype S2056NonzeroTorsion := Fintype.ofFinite _

/-- The root count: prePsi_5 has exactly 12 distinct roots. -/
theorem S2056Root_card : Nat.card S2056Root = 12 := by
  classical
  have h : (s1329RootFinset S1906W 5).card = 12 := by
    simpa [S1906RootCount, S1982Five] using S1982RootCount_five
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  simpa [S2056RootFinset, s1329RootFinset] using h

/-! ## 3. The fibre of the x-coordinate map -/

/-- The fibre of the x-coordinate map over x, restricted to nonzero
5-torsion. -/
noncomputable def S2056Fibre (x : S2056K) : Finset S2056NonzeroTorsion := by
  classical
  exact Finset.univ.filter (fun P : S2056NonzeroTorsion => P.1.1.xCoord = x)

/-- Membership in the fibre. -/
theorem S2056Fibre_mem_iff {x : S2056K} {P : S2056NonzeroTorsion} :
    P ∈ S2056Fibre x ↔ P.1.1.xCoord = x := by
  classical
  rw [S2056Fibre]
  simp

/-- prePsi_5 is nonzero. -/
theorem S2056W_preΨ_ne_zero : S2056W.preΨ (5 : Int) ≠ 0 := by
  simpa [S2056W, S1982Five] using S1906_preΨ_ne_zero S1982Five

/-- Every root of the root finset evaluates prePsi_5 to zero. -/
theorem S2056Root_eval (x : S2056Root) : (S2056W.preΨ (5 : Int)).eval x.1 = 0 :=
  s1329PreΨ_eval_of_mem_roots S2056W S2056W_preΨ_ne_zero
    (by simpa [S2056RootFinset, s1329RootFinset] using x.2)

/-- A root of prePsi_5 is not the x-coordinate of a 2-torsion point. -/
theorem S2056Root_Ψ₂Sq_ne_zero (x : S2056Root) :
    (S2056W.Ψ₂Sq).eval x.1 ≠ 0 :=
  S1906NoTwoTorsionRoots_of_criterion S1982Five (S1924S1906Criterion S1982Five)
    x.1 (by simpa [S2056RootFinset, s1329RootFinset, S1982Five] using x.2)

/-- The x-coordinate is invariant under negation. -/
theorem S2056xCoord_neg (P : S2056W.Point) : (-P).xCoord = P.xCoord := by
  cases P with
  | zero => rfl
  | some x y h => rw [Point.neg_some]; rfl

/-- The x-coordinate fibre is closed under negation. -/
theorem S2056Fibre_neg_mem (x : S2056K) :
    ∀ P ∈ S2056Fibre x, -P ∈ S2056Fibre x := by
  intro P hP
  rw [S2056Fibre_mem_iff] at hP ⊢
  change ((-(P.1.1) : S2056W.Point)).xCoord = x
  rw [S2056xCoord_neg]
  exact hP

/-- Two nonzero points with the same x-coordinate are equal or opposite. -/
theorem S2056_eq_or_eq_neg_of_xCoord_eq {P Q : S2056W.Point}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : P.xCoord = Q.xCoord) : P = Q ∨ P = -Q := by
  cases P with
  | zero => exact absurd rfl hP
  | some px py hp =>
    cases Q with
    | zero => exact absurd rfl hQ
    | some qx qy hq =>
      rw [Point.xCoord_some, Point.xCoord_some] at hx
      have hrep : (Point.some px py hp).xRep = (Point.some qx qy hq).xRep := by
        rw [Point.xRep_some, Point.xRep_some, hx]
      exact Point.eq_or_eq_neg_of_xRep_eq_xRep hrep

/-- Two nonzero 5-torsion points with the same x-coordinate are equal or
opposite, at the level of the subtype of nonzero 5-torsion. -/
theorem S2056_eq_or_eq_neg {P Q : S2056NonzeroTorsion}
    (hx : Q.1.1.xCoord = P.1.1.xCoord) : Q = P ∨ Q = -P := by
  have h := S2056_eq_or_eq_neg_of_xCoord_eq Q.2 P.2 hx
  rcases h with h | h
  · exact Or.inl (Subtype.ext (Subtype.ext h))
  · refine Or.inr (Subtype.ext (Subtype.ext ?_))
    change (Q.1.1 : S2056W.Point) = ((-P.1 : S2056Torsion) : S2056W.Point)
    rw [AddSubgroup.coe_neg]
    exact h

/-- A nonzero 5-torsion point is not its own negative. -/
theorem S2056_ne_neg (P : S2056NonzeroTorsion) : P ≠ -P := by
  intro h
  have hpt : (P.1.1 : S2056W.Point) = -(P.1.1 : S2056W.Point) := by
    have h2 : (P.1 : S2056Torsion) = -P.1 := congrArg Subtype.val h
    have h3 : (P.1.1 : S2056W.Point) = ((-P.1 : S2056Torsion) : S2056W.Point) :=
      congrArg Subtype.val h2
    rwa [AddSubgroup.coe_neg] at h3
  have hp2 : (2 : Nat) • (P.1.1 : S2056W.Point) = 0 := by
    have hsum : (P.1.1 : S2056W.Point) + (P.1.1 : S2056W.Point) = 0 := by
      nth_rewrite 2 [hpt]
      exact add_neg_cancel _
    simpa [two_nsmul] using hsum
  have hp5 : (5 : Nat) • (P.1.1 : S2056W.Point) = 0 := by
    simpa [natCast_zsmul] using P.1.2
  have hdvd2 : addOrderOf (P.1.1 : S2056W.Point) ∣ 2 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hp2
  have hdvd5 : addOrderOf (P.1.1 : S2056W.Point) ∣ 5 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hp5
  have hone : addOrderOf (P.1.1 : S2056W.Point) = 1 := by
    have hg := Nat.dvd_gcd hdvd2 hdvd5
    rw [show Nat.gcd 2 5 = 1 from by norm_num] at hg
    exact Nat.dvd_one.mp hg
  exact P.2 (AddMonoid.addOrderOf_eq_one_iff.mp hone)

/-- The fibre at a root of prePsi_5 is nonempty: a square root of the fibre
quadratic gives a 5-torsion point over that root. -/
theorem S2056Fibre_nonempty (x : S2056Root) : (S2056Fibre x.1).Nonempty := by
  classical
  have hΨ : (S2056W.Ψ₂Sq).eval x.1 ≠ 0 := S2056Root_Ψ₂Sq_ne_zero x
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((S2056W.Ψ₂Sq).eval x.1)
    (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by
    intro h
    apply hΨ
    rw [← hs, h]
    norm_num
  let y : S2056K := (s - (S2056W.a₁ * x.1 + S2056W.a₃)) / 2
  have hy : 2 * y + S2056W.a₁ * x.1 + S2056W.a₃ = s := by
    rw [show y = (s - (S2056W.a₁ * x.1 + S2056W.a₃)) / 2 from rfl]
    field_simp
    ring
  have h2 : (2 : S2056K) ≠ 0 := by
    haveI : CharZero S2056K := inferInstance
    exact_mod_cast (by norm_num : (2 : Nat) ≠ 0)
  have hEq : S2056W.Equation x.1 y :=
    (s1329Equation_iff_sq S2056W h2 x.1 y).mpr (by rw [hy, hs])
  have hns : S2056W.Nonsingular x.1 y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hEq
  have hfive : (5 : Int) • Point.some x.1 y hns = 0 := by
    have hcrit := S1924S1906Criterion S1982Five
    have hev : S2056W.evalDivisionPolynomialAtPoint (5 : Int)
        (Point.some x.1 y hns) = 0 := by
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        S2056W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1
          (by norm_num : ¬ Even (5 : Int))]
      exact S2056Root_eval x
    exact (hcrit (Point.some x.1 y hns)).mpr (by simpa [S1982Five] using hev)
  refine ⟨⟨⟨Point.some x.1 y hns, hfive⟩, Point.some_ne_zero hns⟩, ?_⟩
  rw [S2056Fibre_mem_iff, Point.xCoord_some]

/-- The fibre over a root of prePsi_5 has exactly two points. -/
theorem S2056Fibre_card (x : S2056Root) : (S2056Fibre x.1).card = 2 := by
  classical
  obtain ⟨P, hP⟩ := S2056Fibre_nonempty x
  have hneg : -P ∈ S2056Fibre x.1 := S2056Fibre_neg_mem x.1 P hP
  have hne : P ≠ -P := S2056_ne_neg P
  have hpaircard : ({P, -P} : Finset S2056NonzeroTorsion).card = 2 :=
    Finset.card_pair hne
  have hge : 2 ≤ (S2056Fibre x.1).card := by
    have hsub : ({P, -P} : Finset S2056NonzeroTorsion) ⊆ S2056Fibre x.1 := by
      intro Q hQ
      rw [Finset.mem_insert, Finset.mem_singleton] at hQ
      rcases hQ with rfl | rfl
      · exact hP
      · exact hneg
    have := Finset.card_le_card hsub
    omega
  have hle : (S2056Fibre x.1).card ≤ 2 := by
    have hsub : S2056Fibre x.1 ⊆ ({P, -P} : Finset S2056NonzeroTorsion) := by
      intro Q hQ
      have hxQ : Q.1.1.xCoord = x.1 := S2056Fibre_mem_iff.mp hQ
      have hxP : P.1.1.xCoord = x.1 := S2056Fibre_mem_iff.mp hP
      have h := S2056_eq_or_eq_neg (P := P) (Q := Q) (by rw [hxQ, hxP])
      rcases h with h | h
      · rw [h]
        exact Finset.mem_insert_self _ _
      · rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have := Finset.card_le_card hsub
    omega
  omega

/-! ## 4. The bijection -/

/-- The canonical map from roots of prePsi_5 to pairs {+-P}: send a root to
the (two-element, negation-closed) fibre of the x-coordinate map above it. -/
noncomputable def S2056RootToPair (x : S2056Root) : S2056Pair :=
  ⟨S2056Fibre x.1, S2056Fibre_card x, S2056Fibre_neg_mem x.1⟩

/-- The root-to-pair map is injective. -/
theorem S2056RootToPair_injective : Function.Injective S2056RootToPair := by
  intro x y h
  have hfib : S2056Fibre x.1 = S2056Fibre y.1 := congrArg Subtype.val h
  obtain ⟨P, hP⟩ := S2056Fibre_nonempty x
  have hPy : P ∈ S2056Fibre y.1 := by rw [← hfib]; exact hP
  have hx : P.1.1.xCoord = x.1 := S2056Fibre_mem_iff.mp hP
  have hy : P.1.1.xCoord = y.1 := S2056Fibre_mem_iff.mp hPy
  exact Subtype.ext (by rw [← hx, ← hy])

/-- A nonzero 5-torsion point has x-coordinate a root of prePsi_5. -/
theorem S2056_xCoord_mem_rootFinset_of_torsion {P : S2056W.Point}
    (hP : P ≠ 0) (h5 : (5 : Int) • P = 0) : P.xCoord ∈ S2056RootFinset := by
  have hcrit := S1924S1906Criterion S1982Five
  have hev : S2056W.evalDivisionPolynomialAtPoint (5 : Int) P = 0 :=
    (hcrit P).mp (by simpa [S1982Five] using h5)
  cases P with
  | zero => exact absurd rfl hP
  | some x y hns =>
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some] at hev
    rw [S2056W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1
      (by norm_num : ¬ Even (5 : Int))] at hev
    rw [S2056RootFinset, Multiset.mem_toFinset, Polynomial.mem_roots S2056W_preΨ_ne_zero]
    simpa using hev

/-- The root-to-pair map is surjective. -/
theorem S2056RootToPair_surjective : Function.Surjective S2056RootToPair := by
  classical
  rintro ⟨S, hcard, hneg⟩
  obtain ⟨P, hPS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hne : P ≠ -P := S2056_ne_neg P
  have hPneg : -P ∈ S := hneg P hPS
  have hSeq : S = {P, -P} := by
    have hsub : ({P, -P} : Finset S2056NonzeroTorsion) ⊆ S := by
      intro Q hQ
      rw [Finset.mem_insert, Finset.mem_singleton] at hQ
      rcases hQ with rfl | rfl
      · exact hPS
      · exact hPneg
    have hle : S.card ≤ ({P, -P} : Finset S2056NonzeroTorsion).card := by
      rw [hcard, Finset.card_pair hne]
    have h1 : ({P, -P} : Finset S2056NonzeroTorsion) = S :=
      Finset.eq_of_subset_of_card_le hsub hle
    exact h1.symm
  have hmem : P.1.1.xCoord ∈ S2056RootFinset :=
    S2056_xCoord_mem_rootFinset_of_torsion P.2 P.1.2
  refine ⟨⟨P.1.1.xCoord, hmem⟩, ?_⟩
  have hPfib : P ∈ S2056Fibre P.1.1.xCoord := by
    rw [S2056Fibre_mem_iff]
  have hnegfib : -P ∈ S2056Fibre P.1.1.xCoord :=
    S2056Fibre_neg_mem _ _ hPfib
  have hsub : ({P, -P} : Finset S2056NonzeroTorsion) ⊆ S2056Fibre P.1.1.xCoord := by
    intro Q hQ
    rw [Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl
    · exact hPfib
    · exact hnegfib
  have hle : (S2056Fibre P.1.1.xCoord).card ≤
      ({P, -P} : Finset S2056NonzeroTorsion).card := by
    rw [S2056Fibre_card ⟨P.1.1.xCoord, hmem⟩, Finset.card_pair hne]
  have hEq : ({P, -P} : Finset S2056NonzeroTorsion) = S2056Fibre P.1.1.xCoord :=
    Finset.eq_of_subset_of_card_le hsub hle
  have hfib : S2056Fibre P.1.1.xCoord = S := by rw [← hEq, hSeq]
  exact Subtype.ext hfib

/-- D5(1): the twelve roots of prePsi_5 are in canonical bijection with the
twelve pairs {+-P} of nonzero 5-torsion points. -/
noncomputable def S2056RootPairEquiv : S2056Root ≃ S2056Pair :=
  Equiv.ofBijective S2056RootToPair
    ⟨S2056RootToPair_injective, S2056RootToPair_surjective⟩

/-- Consequently there are exactly twelve pairs {+-P}. -/
theorem S2056Pair_card : Nat.card S2056Pair = 12 := by
  rw [← Nat.card_congr S2056RootPairEquiv, S2056Root_card]

/-! ## 5. Galois equivariance

Let sigma be an F'-algebra automorphism of K.  It acts on the points of E'
(through the group homomorphism S2056PointMap) and hence on the nonzero
5-torsion and on the pairs.  The root-to-pair bijection is canonical, so it
intertwines the two actions. -/

/-- The action of an F'-algebra automorphism of K on the points of E'. -/
noncomputable def S2056PointMap (σ : S2056K ≃ₐ[S1720Field] S2056K) :
    S2056W.Point →+ S2056W.Point :=
  Point.map (W' := S1720Curve.curve) σ.toAlgHom

/-- The point map acts on x-coordinates by sigma. -/
theorem S2056PointMap_xCoord (σ : S2056K ≃ₐ[S1720Field] S2056K) (P : S2056W.Point) :
    (S2056PointMap σ P).xCoord = σ P.xCoord :=
  Point.xCoord_map (W := S1720Curve.curve) σ.toAlgHom P

/-- The point map preserves 5-torsion. -/
theorem S2056PointMap_torsion (σ : S2056K ≃ₐ[S1720Field] S2056K) {P : S2056W.Point}
    (hP : (5 : Int) • P = 0) : (5 : Int) • S2056PointMap σ P = 0 := by
  rw [← map_zsmul, hP, map_zero]

/-- The point map is injective. -/
theorem S2056PointMap_injective (σ : S2056K ≃ₐ[S1720Field] S2056K) :
    Function.Injective (S2056PointMap σ) :=
  Point.map_injective (W' := S1720Curve.curve) σ.toAlgHom

/-- The action of sigma on the nonzero 5-torsion. -/
noncomputable def S2056NonzeroTorsionMap (σ : S2056K ≃ₐ[S1720Field] S2056K) :
    S2056NonzeroTorsion → S2056NonzeroTorsion :=
  fun P =>
    ⟨⟨S2056PointMap σ P.1.1, S2056PointMap_torsion σ P.1.2⟩, by
      intro h
      have h' : S2056PointMap σ P.1.1 = 0 := h
      have h1 : S2056PointMap σ P.1.1 = S2056PointMap σ 0 := by
        rw [h', map_zero]
      exact P.2 (S2056PointMap_injective σ h1)⟩

/-- The action on the nonzero 5-torsion commutes with negation. -/
theorem S2056NonzeroTorsionMap_neg (σ : S2056K ≃ₐ[S1720Field] S2056K)
    (P : S2056NonzeroTorsion) :
    S2056NonzeroTorsionMap σ (-P) = -(S2056NonzeroTorsionMap σ P) := by
  apply Subtype.ext
  apply Subtype.ext
  show S2056PointMap σ ((-P).1.1) = -S2056PointMap σ P.1.1
  have h1 : ((-P).1.1 : S2056W.Point) = -(P.1.1 : S2056W.Point) := rfl
  rw [h1]
  exact map_neg (S2056PointMap σ) P.1.1

/-- The action on the nonzero 5-torsion is injective. -/
theorem S2056NonzeroTorsionMap_injective (σ : S2056K ≃ₐ[S1720Field] S2056K) :
    Function.Injective (S2056NonzeroTorsionMap σ) := by
  intro P Q h
  have h1 : (P.1.1 : S2056W.Point) = (Q.1.1 : S2056W.Point) := by
    have h2 := congrArg (fun R : S2056NonzeroTorsion => (R.1.1 : S2056W.Point)) h
    exact S2056PointMap_injective σ h2
  exact Subtype.ext (Subtype.ext h1)

/-- The action of sigma on the pairs of nonzero 5-torsion. -/
noncomputable def S2056PairMap (σ : S2056K ≃ₐ[S1720Field] S2056K) :
    S2056Pair → S2056Pair :=
  fun S => ⟨S.1.image (S2056NonzeroTorsionMap σ), by
    classical
    refine ⟨?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (S2056NonzeroTorsionMap_injective σ)]
      exact S.2.1
    · intro Q hQ
      rw [Finset.mem_image] at hQ ⊢
      obtain ⟨P, hP, rfl⟩ := hQ
      exact ⟨-P, S.2.2 P hP, S2056NonzeroTorsionMap_neg σ P⟩⟩

/-- A root of prePsi_5 is sent to a root of prePsi_5 by sigma. -/
theorem S2056Root_smul_mem (σ : S2056K ≃ₐ[S1720Field] S2056K) (x : S2056Root) :
    σ x.1 ∈ S2056RootFinset := by
  obtain ⟨P, hP⟩ := S2056Fibre_nonempty x
  have hx : P.1.1.xCoord = x.1 := S2056Fibre_mem_iff.mp hP
  have hne : S2056PointMap σ P.1.1 ≠ 0 := by
    intro h
    have h1 : S2056PointMap σ P.1.1 = S2056PointMap σ 0 := by
      rw [h, map_zero]
    exact P.2 (S2056PointMap_injective σ h1)
  have h5 : (5 : Int) • S2056PointMap σ P.1.1 = 0 := S2056PointMap_torsion σ P.1.2
  have hmem := S2056_xCoord_mem_rootFinset_of_torsion hne h5
  rwa [S2056PointMap_xCoord σ P.1.1, hx] at hmem

/-- The action of sigma on the roots of prePsi_5. -/
noncomputable def S2056RootMap (σ : S2056K ≃ₐ[S1720Field] S2056K) (x : S2056Root) :
    S2056Root :=
  ⟨σ x.1, S2056Root_smul_mem σ x⟩

/-- **D5(1), equivariant form: the root-to-pair bijection commutes with the
action of every F'-automorphism of K.** -/
theorem S2056RootToPair_equivariant (σ : S2056K ≃ₐ[S1720Field] S2056K)
    (x : S2056Root) :
    S2056RootToPair (S2056RootMap σ x) = S2056PairMap σ (S2056RootToPair x) := by
  classical
  apply Subtype.ext
  change S2056Fibre (σ x.1) =
    (S2056Fibre x.1).image (S2056NonzeroTorsionMap σ)
  have hsub : (S2056Fibre x.1).image (S2056NonzeroTorsionMap σ) ⊆
      S2056Fibre (σ x.1) := by
    intro Q hQ
    rw [Finset.mem_image] at hQ
    obtain ⟨P, hP, rfl⟩ := hQ
    rw [S2056Fibre_mem_iff] at hP ⊢
    change (S2056PointMap σ P.1.1).xCoord = σ x.1
    rw [S2056PointMap_xCoord, hP]
  have hcard : ((S2056Fibre x.1).image (S2056NonzeroTorsionMap σ)).card = 2 := by
    rw [Finset.card_image_of_injective _ (S2056NonzeroTorsionMap_injective σ),
      S2056Fibre_card x]
  have hcard2 : (S2056Fibre (σ x.1)).card = 2 :=
    S2056Fibre_card (S2056RootMap σ x)
  have hle : (S2056Fibre (σ x.1)).card ≤
      ((S2056Fibre x.1).image (S2056NonzeroTorsionMap σ)).card := by
    rw [hcard2, hcard]
  exact (Finset.eq_of_subset_of_card_le hsub hle).symm

/-- The bijection itself is equivariant. -/
theorem S2056RootPairEquiv_equivariant (σ : S2056K ≃ₐ[S1720Field] S2056K)
    (x : S2056Root) :
    S2056RootPairEquiv (S2056RootMap σ x) =
      S2056PairMap σ (S2056RootPairEquiv x) :=
  S2056RootToPair_equivariant σ x

/-- The root-to-pair map sends a root to the pair {P, -P} of any point over it. -/
theorem S2056RootToPair_apply (x : S2056Root) (P : S2056NonzeroTorsion)
    (hP : P ∈ S2056Fibre x.1) : (S2056RootToPair x).1 = {P, -P} := by
  classical
  have hPfib : P ∈ S2056Fibre x.1 := hP
  have hnegfib : -P ∈ S2056Fibre x.1 := S2056Fibre_neg_mem x.1 P hPfib
  have hne : P ≠ -P := S2056_ne_neg P
  have hsub : S2056Fibre x.1 ⊆ ({P, -P} : Finset S2056NonzeroTorsion) := by
    intro Q hQ
    have hxQ : Q.1.1.xCoord = x.1 := S2056Fibre_mem_iff.mp hQ
    have hxP : P.1.1.xCoord = x.1 := S2056Fibre_mem_iff.mp hP
    have h := S2056_eq_or_eq_neg (P := P) (Q := Q) (by rw [hxQ, hxP])
    rcases h with h | h
    · rw [h]
      exact Finset.mem_insert_self _ _
    · rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hle : ({P, -P} : Finset S2056NonzeroTorsion).card ≤ (S2056Fibre x.1).card := by
    rw [Finset.card_pair hne, S2056Fibre_card x]
  exact Finset.eq_of_subset_of_card_le hsub hle

/-! ## 6. Axiom footprint -/

#print axioms S2056Torsion_card
#print axioms S2056Root_card
#print axioms S2056Fibre_nonempty
#print axioms S2056Fibre_neg_mem
#print axioms S2056Fibre_card
#print axioms S2056RootToPair
#print axioms S2056RootToPair_injective
#print axioms S2056RootToPair_surjective
#print axioms S2056RootPairEquiv
#print axioms S2056Pair_card
#print axioms S2056PointMap
#print axioms S2056PointMap_xCoord
#print axioms S2056NonzeroTorsionMap
#print axioms S2056NonzeroTorsionMap_injective
#print axioms S2056PairMap
#print axioms S2056Root_smul_mem
#print axioms S2056RootMap
#print axioms S2056RootToPair_equivariant
#print axioms S2056RootPairEquiv_equivariant
#print axioms S2056RootToPair_apply

end LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual


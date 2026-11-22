/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1361DivisionCriterionActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import tmp.sheaf.xif.paper.S1366PrePsiSeparabilityFix
import LeanFormal.IUT.ABCBridge.Galois.EllipticPrimeTorsionCardinality

/-!
# S1906: the actual rank-two l-torsion module of E'/F'

S1894 reduced the D5 large-image input on the actual curve E'/F' of S1720 to
the rank-two basis gap S1725RankTwoBasisGap l together with a basis-free
large-image condition.  This file attacks the basis gap itself.

## What is proved here (unconditional)

* The basis gap is exactly the numerical cardinality statement
  Nat.card E'[l] = l ^ 2 (S1906RankTwoBasisGap_iff_natCard).  No finiteness
  hypothesis is needed: an infinite type has Nat.card = 0, while l ^ 2 is nonzero.
* The basis gap is exactly the finrank statement
  Module.finrank (ZMod l) E'[l] = 2 (S1906RankTwoBasisGap_iff_finrank), again
  with no finiteness hypothesis (an infinite module has finrank zero).
* A rank-two basis makes E'[l] a finite free ZMod l-module
  (S1906Finite_of_basisGap; freeness is automatic over a field).

So the whole remaining mathematical content of the basis gap is the single
arithmetic identity Nat.card E'[l] = l ^ 2; no hidden basis or extra
hypothesis remains.

## The division-polynomial reduction

Let W = E'_K be the base change of E' to an algebraic closure K of F'.  The
file specialises the division-polynomial API of S1329/S1361 to W:

* S1906Criterion l is the group-law criterion
  l • P = 0 iff psi_l(P) = 0 for all P : W.Point;
* S1906RootCount l says that the odd l-division polynomial prePsi_l has its
  full geometric number (l ^ 2 - 1) / 2 of distinct roots in K.

Under the criterion, the basis gap is equivalent to the root count
(S1906RankTwoBasisGap_iff_rootCount_of_criterion).  Moreover the criterion is
exactly the conjunction of the two halves isolated in S1361:

* s1361Detection W l (torsion implies psi_l vanishes), which S1361 derives from
  the still-missing Mathlib coordinate formula x([n]P) = Phi_n/psi_n^2;
* s1361ZeroCriterion W l (psi_l vanishes implies torsion).

## The exact first missing statement

Mathlib (v4.32.2) has the division polynomials psi_n, phi_n, Phi_n, prePsi_n,
PsiSq_n and their degrees, but it has:

1. no coordinate formula x([n]P) = Phi_n(P)/psi_n(P)^2 for n >= 4
   (s1361XCoordinateFormula; the bivariate omega_n needed for the
   y-coordinate is an explicit TODO in Mathlib);
2. no reverse detection psi_n(P) = 0 implies n • P = 0 (s1361ZeroCriterion);
3. no separability/root count for prePsi_l in characteristic zero.  This is
   exactly the tree's S1366/S1420 input S1366GenericOddPreΨSeparableInput
   (the characteristic-zero odd part of TauCeti's separable_prePsi, which is
   not importable at this Mathlib pin).

The file records these as explicit hypotheses and proves that they imply the
actual basis gap; no axiom, sorry or opaque declaration is introduced, and no
basis is constructed from nothing.  In particular:

* detection alone gives |E'[l]| <= l^2 and finiteness
  (S1906NatCard_le_sq_of_detection, S1906Finite_of_detection);
* under the full group-law criterion, the basis gap is equivalent to the root
  count of prePsi_l (S1906RankTwoBasisGap_iff_rootCount_of_criterion);
* separability of prePsi_l gives the root count (S1906RootCount_of_separable),
  hence, together with the x-coordinate formula and reverse detection, the
  basis gap (S1906BasisGap_of_xCoordinateFormula_zeroCriterion_separable).

## Main results

* S1906RankTwoBasisGap_iff_natCard
* S1906RankTwoBasisGap_iff_finrank
* S1906Finite_of_basisGap
* S1906NatCard_eq_sq_of_criterion_rootCount
* S1906RankTwoBasisGap_iff_rootCount_of_criterion
* S1906Criterion_iff_detection_and_zero
* S1906BasisGap_of_xCoordinateFormula_zeroCriterion_rootCount
* S1906NatCard_le_sq_of_detection
* S1906Finite_of_detection
* S1906RootCount_of_separable
* S1906RootCount_of_genericPreΨSeparable
* S1906BasisGap_of_xCoordinateFormula_zeroCriterion_separable
* S1906BasisGap_of_xCoordinateFormula_zeroCriterion_genericSeparable
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual
open LeanFormal.IUT.XiFPaper.S1361DivisionCriterionActual
open LeanFormal.IUT.XiFPaper.S1366PrePsiSeparabilityFix
open Polynomial

/-! ## 1. The actual curve over the algebraic closure -/

/-- The algebraic closure of the actual number field F'. -/
abbrev S1906K : Type := AlgebraicClosure S1720Field

/-- Classical decidable equality on the algebraic closure. -/
local instance S1906KDecEq : DecidableEq S1906K := Classical.decEq _

/-- The actual curve E' base changed to the algebraic closure of F'. -/
abbrev S1906W : WeierstrassCurve.Affine S1906K := S1720Curve.curve.baseChange S1906K

/-- The projective points of E' over the algebraic closure are definitionally
the projective points of the base-changed Weierstrass curve. -/
theorem S1906ProjectivePoint_eq :
    S1720Curve.AlgebraicClosurePoint = WeierstrassCurve.Projective.Point S1906W :=
  rfl

/-- The l-torsion carrier is definitionally the torsion-by-l subgroup of the
actual projective point group. -/
theorem S1906LTorsion_eq (l : PrimeGeFive) :
    S1720Curve.LTorsion l =
      AddSubgroup.torsionBy (WeierstrassCurve.Projective.Point S1906W) l.value :=
  rfl

/-- The additive equivalence between projective and affine points of E' over the
algebraic closure. -/
noncomputable def S1906ProjAffineEquiv :
    WeierstrassCurve.Projective.Point S1906W ≃+ WeierstrassCurve.Affine.Point S1906W :=
  WeierstrassCurve.Projective.Point.toAffineAddEquiv S1906W

/-- The projective l-torsion carrier and the affine l-torsion carrier have the
same cardinality. -/
theorem S1906NatCard_LTorsion_eq_affine (l : PrimeGeFive) :
    Nat.card (S1720Curve.LTorsion l) =
      Nat.card (AddSubgroup.torsionBy S1906W.Point (l.value : ℤ)) :=
  s1329NatCard_torsionBy_congr S1906ProjAffineEquiv (l.value : ℤ)

/-! ## 2. Rank two is exactly the cardinality l ^ 2 -/

/-- The type Fin 2 -> ZMod l has cardinality l ^ 2. -/
theorem S1906NatCard_fin_two (l : PrimeGeFive) :
    Nat.card (Fin 2 → ZMod l.value) = l.value ^ 2 := by
  rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]

/-- A rank-two basis forces Nat.card E'[l] = l ^ 2. -/
theorem S1906NatCard_eq_sq_of_basis (l : PrimeGeFive)
    (b : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] S1720Curve.LTorsion l) :
    Nat.card (S1720Curve.LTorsion l) = l.value ^ 2 := by
  rw [← Nat.card_congr b.toEquiv]
  exact S1906NatCard_fin_two l

/-- Nat.card E'[l] = l ^ 2 already forces finiteness: an infinite type has
cardinality zero. -/
theorem S1906Finite_of_natCard (l : PrimeGeFive)
    (h : Nat.card (S1720Curve.LTorsion l) = l.value ^ 2) :
    Finite (S1720Curve.LTorsion l) := by
  by_contra hfin
  haveI : Infinite (S1720Curve.LTorsion l) := not_finite_iff_infinite.mp hfin
  rw [Nat.card_eq_zero_of_infinite] at h
  exact pow_ne_zero 2 l.prime.ne_zero h.symm

/-- The cardinality l ^ 2 produces a rank-two basis.  This is the
linear-algebra engine: a finite ZMod l-module of cardinality l ^ 2 has
dimension two. -/
theorem S1906Basis_of_natCard (l : PrimeGeFive)
    (h : Nat.card (S1720Curve.LTorsion l) = l.value ^ 2) :
    Nonempty ((Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] S1720Curve.LTorsion l) := by
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  haveI : Finite (S1720Curve.LTorsion l) := S1906Finite_of_natCard l h
  haveI : Module.Finite (ZMod l.value) (S1720Curve.LTorsion l) := Module.Finite.of_finite
  have hpow : l.value ^ 2 =
      l.value ^ Module.finrank (ZMod l.value) (S1720Curve.LTorsion l) := by
    rw [← h, Module.natCard_eq_pow_finrank (K := ZMod l.value)
      (V := S1720Curve.LTorsion l), Nat.card_zmod]
  have hl : 1 < l.value := l.prime.one_lt
  have hfr : Module.finrank (ZMod l.value) (S1720Curve.LTorsion l) = 2 := by
    rcases lt_trichotomy (Module.finrank (ZMod l.value) (S1720Curve.LTorsion l)) 2 with
      hlt | heq | hgt
    · have hlt' : l.value ^ Module.finrank (ZMod l.value) (S1720Curve.LTorsion l) <
          l.value ^ 2 := Nat.pow_lt_pow_right hl hlt
      omega
    · exact heq
    · have hgt' : l.value ^ 2 <
          l.value ^ Module.finrank (ZMod l.value) (S1720Curve.LTorsion l) :=
        Nat.pow_lt_pow_right hl hgt
      omega
  exact (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq).mpr (by
    rw [Module.finrank_fin_fun]
    exact hfr.symm)

/-- Exact form of the basis gap: it is the single cardinality identity
Nat.card E'[l] = l ^ 2.  No finiteness hypothesis is required. -/
theorem S1906RankTwoBasisGap_iff_natCard (l : PrimeGeFive) :
    S1725RankTwoBasisGap l ↔ Nat.card (S1720Curve.LTorsion l) = l.value ^ 2 := by
  constructor
  · rintro ⟨b⟩
    exact S1906NatCard_eq_sq_of_basis l b
  · intro h
    exact S1906Basis_of_natCard l h

/-- Exact finrank form of the basis gap.  No finiteness hypothesis is
required, since an infinite module has finrank zero. -/
theorem S1906RankTwoBasisGap_iff_finrank (l : PrimeGeFive) :
    S1725RankTwoBasisGap l ↔
      Module.finrank (ZMod l.value) (S1720Curve.LTorsion l) = 2 := by
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  constructor
  · rintro ⟨b⟩
    haveI : Finite (S1720Curve.LTorsion l) := Finite.of_equiv _ b.toEquiv
    haveI : Module.Finite (ZMod l.value) (S1720Curve.LTorsion l) := Module.Finite.of_finite
    have h := b.finrank_eq
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  · intro hfr
    haveI : Module.Finite (ZMod l.value) (S1720Curve.LTorsion l) :=
      Module.finite_of_finrank_eq_succ (n := 1) (by simpa using hfr)
    exact (FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq).mpr (by
      rw [Module.finrank_fin_fun]
      exact hfr.symm)

/-- A rank-two basis makes the actual l-torsion carrier finite. -/
theorem S1906Finite_of_basisGap (l : PrimeGeFive) (h : S1725RankTwoBasisGap l) :
    Finite (S1720Curve.LTorsion l) := by
  obtain ⟨b⟩ := h
  exact Finite.of_equiv _ b.toEquiv

/-- A rank-two basis makes the actual l-torsion carrier a finite module. -/
theorem S1906ModuleFinite_of_basisGap (l : PrimeGeFive) (h : S1725RankTwoBasisGap l) :
    Module.Finite (ZMod l.value) (S1720Curve.LTorsion l) := by
  haveI : Finite (S1720Curve.LTorsion l) := S1906Finite_of_basisGap l h
  exact Module.Finite.of_finite

/-- **A rank-two basis makes E'[l] a finite free ZMod l-module of rank two.**
Freeness is automatic over the field ZMod l; the rank is
S1906RankTwoBasisGap_iff_finrank. -/
theorem S1906FiniteFreeRankTwo_of_basisGap (l : PrimeGeFive)
    (h : S1725RankTwoBasisGap l) :
    Module.Finite (ZMod l.value) (S1720Curve.LTorsion l) ∧
      Module.Free (ZMod l.value) (S1720Curve.LTorsion l) ∧
      Module.finrank (ZMod l.value) (S1720Curve.LTorsion l) = 2 := by
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  exact ⟨S1906ModuleFinite_of_basisGap l h, inferInstance,
    (S1906RankTwoBasisGap_iff_finrank l).mp h⟩

/-- The cardinality l ^ 2 alone makes E'[l] a finite free ZMod l-module of
rank two. -/
theorem S1906FiniteFreeRankTwo_of_natCard (l : PrimeGeFive)
    (h : Nat.card (S1720Curve.LTorsion l) = l.value ^ 2) :
    Module.Finite (ZMod l.value) (S1720Curve.LTorsion l) ∧
      Module.Free (ZMod l.value) (S1720Curve.LTorsion l) ∧
      Module.finrank (ZMod l.value) (S1720Curve.LTorsion l) = 2 :=
  S1906FiniteFreeRankTwo_of_basisGap l
    ((S1906RankTwoBasisGap_iff_natCard l).mpr h)


/-! ## 3. The division-polynomial criterion and the root count -/

/-- The actual group-law criterion for the odd prime l: l-torsion is exactly the
vanishing locus of psi_l on the affine model E'_K. -/
def S1906Criterion (l : PrimeGeFive) : Prop :=
  s1329DivisionCriterion S1906W l.value

/-- The first half of the criterion: every l-torsion point is a root of psi_l. -/
def S1906Detection (l : PrimeGeFive) : Prop :=
  s1361Detection S1906W (l.value : ℤ)

/-- The second half of the criterion: every root of psi_l is l-torsion. -/
def S1906ZeroCriterion (l : PrimeGeFive) : Prop :=
  s1361ZeroCriterion S1906W (l.value : ℤ)

/-- The root count of the odd l-division polynomial: prePsi_l has its full
geometric number (l ^ 2 - 1) / 2 of distinct roots in the algebraic closure. -/
def S1906RootCount (l : PrimeGeFive) : Prop :=
  (s1329RootFinset S1906W l.value).card = (l.value ^ 2 - 1) / 2

/-- The group-law criterion is exactly the conjunction of the two halves
isolated in S1361. -/
theorem S1906Criterion_iff (l : PrimeGeFive) :
    S1906Criterion l ↔ S1906Detection l ∧ S1906ZeroCriterion l :=
  s1361Criterion_iff S1906W (l.value : ℤ)

/-- Two is nonzero in the characteristic-zero closure. -/
theorem S1906_two_ne_zero : (2 : S1906K) ≠ 0 := by
  haveI : CharZero S1906K := inferInstance
  exact_mod_cast (by norm_num : (2 : ℕ) ≠ 0)

/-- The prime l is nonzero in the characteristic-zero closure. -/
theorem S1906_l_ne_zero (l : PrimeGeFive) : (l.value : S1906K) ≠ 0 := by
  haveI : CharZero S1906K := inferInstance
  exact_mod_cast l.prime.ne_zero

/-- The prime l is odd as an integer. -/
theorem S1906_not_even (l : PrimeGeFive) : ¬ Even (l.value : ℤ) := by
  rw [Int.even_coe_nat, Nat.not_even_iff_odd]
  exact l.prime.odd_of_ne_two (by have := l.ge_five; omega)

/-- prePsi_l is a nonzero polynomial. -/
theorem S1906_preΨ_ne_zero (l : PrimeGeFive) :
    S1906W.preΨ (l.value : ℤ) ≠ 0 :=
  WeierstrassCurve.preΨ_ne_zero (W := S1906W) (by
    haveI : CharZero S1906K := inferInstance
    exact_mod_cast l.prime.ne_zero)

/-- Under the group-law criterion, no root of prePsi_l is the x-coordinate of a
2-torsion point: such a point would be both 2- and l-torsion, hence zero. -/
theorem S1906NoTwoTorsionRoots_of_criterion (l : PrimeGeFive)
    (hcrit : S1906Criterion l) :
    ∀ x ∈ s1329RootFinset S1906W l.value,
      (S1906W.Ψ₂Sq).eval x ≠ 0 := by
  classical
  intro x hx hc
  have h2 : (2 : S1906K) ≠ 0 := S1906_two_ne_zero
  have hodd : ¬ Even (l.value : ℤ) := S1906_not_even l
  have hpre : S1906W.preΨ (l.value : ℤ) ≠ 0 := S1906_preΨ_ne_zero l
  set y0 : S1906K := (-(S1906W.a₁ * x + S1906W.a₃)) / 2 with hy0
  have hy0eq : 2 * y0 + S1906W.a₁ * x + S1906W.a₃ = 0 := by
    rw [hy0]; field_simp; ring
  have hEq : S1906W.Equation x y0 :=
    (s1329Equation_iff_sq S1906W h2 x y0).mpr (by
      rw [hy0eq, hc]; ring)
  have hns : S1906W.Nonsingular x y0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hEq
  have hψl : (S1906W.preΨ (l.value : ℤ)).eval x = 0 :=
    s1329PreΨ_eval_of_mem_roots S1906W hpre hx
  have hltor : (l.value : ℤ) •
      WeierstrassCurve.Affine.Point.some x y0 hns = 0 := by
    rw [hcrit]
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      S1906W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hodd]
    exact hψl
  have htwo : (2 : ℕ) •
      WeierstrassCurve.Affine.Point.some x y0 hns = 0 := by
    refine (S1906W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero _).mpr ?_
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      WeierstrassCurve.evalDivisionPolynomial_two]
    exact hy0eq
  have hltor' : l.value •
      WeierstrassCurve.Affine.Point.some x y0 hns = 0 := by
    simpa [natCast_zsmul] using hltor
  have hdvd2 : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) ∣ 2 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
  have hdvdl : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) ∣ l.value :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hltor'
  have hcop : Nat.Coprime 2 l.value :=
    (Nat.coprime_primes Nat.prime_two l.prime).mpr (by have := l.ge_five; omega)
  have hone : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) = 1 := by
    have hgcd : addOrderOf (WeierstrassCurve.Affine.Point.some x y0 hns) ∣
        Nat.gcd 2 l.value := Nat.dvd_gcd hdvd2 hdvdl
    rw [hcop] at hgcd
    exact Nat.dvd_one.mp hgcd
  exact WeierstrassCurve.Affine.Point.some_ne_zero hns
    (AddMonoid.addOrderOf_eq_one_iff.mp hone)

/-- Under the criterion, the actual l-torsion has one point at infinity plus two
points over each distinct root of prePsi_l. -/
theorem S1906NatCard_eq (l : PrimeGeFive) (hcrit : S1906Criterion l) :
    Nat.card (S1720Curve.LTorsion l) =
      1 + 2 * (s1329RootFinset S1906W l.value).card := by
  rw [S1906NatCard_LTorsion_eq_affine l]
  exact s1329NatCard_torsionBy_eq S1906W l.value S1906_two_ne_zero hcrit
    (S1906_not_even l) (S1906_preΨ_ne_zero l)
    (S1906NoTwoTorsionRoots_of_criterion l hcrit)

/-- Under the criterion, the cardinality l ^ 2 is exactly the full root count. -/
theorem S1906NatCard_eq_sq_iff_rootCount (l : PrimeGeFive)
    (hcrit : S1906Criterion l) :
    Nat.card (S1720Curve.LTorsion l) = l.value ^ 2 ↔ S1906RootCount l := by
  constructor
  · intro h
    rw [S1906NatCard_eq l hcrit] at h
    have hoddl : Odd l.value :=
      l.prime.odd_of_ne_two (by have := l.ge_five; omega)
    have hN : Odd (l.value ^ 2) := s1329Odd_sq hoddl
    exact s1329TwoMulEqDiv hN (s1329TwoMulOfOneAdd h)
  · intro hroot
    rw [S1906NatCard_eq l hcrit]
    have hoddl : Odd l.value :=
      l.prime.odd_of_ne_two (by have := l.ge_five; omega)
    have hN : Odd (l.value ^ 2) := s1329Odd_sq hoddl
    have h2a : 2 * (s1329RootFinset S1906W l.value).card = l.value ^ 2 - 1 :=
      s1329DivEqTwoMul hN hroot
    exact s1329OneAddTwoMul h2a (pow_pos l.prime.pos 2)

/-- **Sharp reduction.**  Under the group-law criterion, the actual rank-two
basis gap is *exactly* the root count of the odd l-division polynomial. -/
theorem S1906RankTwoBasisGap_iff_rootCount_of_criterion (l : PrimeGeFive)
    (hcrit : S1906Criterion l) :
    S1725RankTwoBasisGap l ↔ S1906RootCount l :=
  (S1906RankTwoBasisGap_iff_natCard l).trans
    (S1906NatCard_eq_sq_iff_rootCount l hcrit)

/-- **Conditional closure from detection, reverse detection and the root
count.**  These are the three classical inputs that the division-polynomial
route needs; no other hypothesis is used. -/
theorem S1906BasisGap_of_detection_zeroCriterion_rootCount (l : PrimeGeFive)
    (hdet : S1906Detection l) (hzero : S1906ZeroCriterion l)
    (hroot : S1906RootCount l) : S1725RankTwoBasisGap l := by
  have hcrit : S1906Criterion l := (S1906Criterion_iff l).mpr ⟨hdet, hzero⟩
  exact (S1906RankTwoBasisGap_iff_rootCount_of_criterion l hcrit).mpr hroot

/-- **Conditional closure from the Mathlib-missing x-coordinate formula, reverse
detection and the root count.**  This is the precise dependency of the present
division-polynomial route on missing library mathematics. -/
theorem S1906BasisGap_of_xCoordinateFormula_zeroCriterion_rootCount
    (l : PrimeGeFive) (hX : s1361XCoordinateFormula S1906W (l.value : ℤ))
    (hzero : S1906ZeroCriterion l) (hroot : S1906RootCount l) :
    S1725RankTwoBasisGap l := by
  have hdet : S1906Detection l :=
    s1361Detection_of_xCoordinateFormula S1906W hX
  exact S1906BasisGap_of_detection_zeroCriterion_rootCount l hdet hzero hroot

/-- The numerical statement that is *exactly* equivalent to the basis gap. -/
def S1906TorsionCardinality (l : PrimeGeFive) : Prop :=
  Nat.card (S1720Curve.LTorsion l) = l.value ^ 2

/-- The basis gap and the cardinality statement are the same proposition. -/
theorem S1906TorsionCardinality_iff_basisGap (l : PrimeGeFive) :
    S1906TorsionCardinality l ↔ S1725RankTwoBasisGap l :=
  (S1906RankTwoBasisGap_iff_natCard l).symm


/-! ## 4. Detection alone gives the upper bound |E'[l]| <= l ^ 2 -/

/-- The explicit additive equivalence between the projective l-torsion carrier
and the affine one. -/
noncomputable def S1906TorsionEquiv (l : PrimeGeFive) :
    S1720Curve.LTorsion l ≃
      AddSubgroup.torsionBy S1906W.Point (l.value : ℤ) where
  toFun P :=
    ⟨S1906ProjAffineEquiv P.1, by
      have hP : (l.value : ℤ) • P.1 = 0 := P.2
      show (l.value : ℤ) • S1906ProjAffineEquiv P.1 = 0
      rw [← map_zsmul, hP, map_zero]⟩
  invFun Q :=
    ⟨S1906ProjAffineEquiv.symm Q.1, by
      have hQ : (l.value : ℤ) • Q.1 = 0 := Q.2
      show (l.value : ℤ) • S1906ProjAffineEquiv.symm Q.1 = 0
      rw [← map_zsmul, hQ, map_zero]⟩
  left_inv P := by ext; simp
  right_inv Q := by ext; simp

/-- Under detection, every affine l-torsion point is one of the explicit
division-locus candidates: the point at infinity, or (x, y) with x a root of
prePsi_l and y a root of the fibre quadratic. -/
theorem S1906TorsionAffine_mem_candidates (l : PrimeGeFive)
    (hdet : S1906Detection l) (P : S1906W.Point)
    (hP : P ∈ AddSubgroup.torsionBy S1906W.Point (l.value : ℤ)) :
    P ∈ s1329DivisionCandidates S1906W l.value := by
  classical
  have hodd : ¬ Even (l.value : ℤ) := S1906_not_even l
  have hpre : S1906W.preΨ (l.value : ℤ) ≠ 0 := S1906_preΨ_ne_zero l
  rcases P with _ | ⟨x, y, hns⟩
  · rw [s1329DivisionCandidates_mem]
    exact Or.inl rfl
  · have hz : (l.value : ℤ) •
        WeierstrassCurve.Affine.Point.some x y hns = 0 := by
      have h' : l.value •
          WeierstrassCurve.Affine.Point.some x y hns = 0 :=
        (AddSubgroup.torsionBy.nsmul_iff).mp hP
      simpa [natCast_zsmul] using h'
    have hev : S1906W.evalDivisionPolynomialAtPoint (l.value : ℤ)
        (WeierstrassCurve.Affine.Point.some x y hns) = 0 :=
      hdet _ hz
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      S1906W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1 hodd] at hev
    have hx : x ∈ s1329RootFinset S1906W l.value := by
      rw [s1329RootFinset, Multiset.mem_toFinset, Polynomial.mem_roots hpre]
      exact hev
    have hy : y ∈ (s1329FibreQuadratic S1906W x).roots.toFinset := by
      rw [Multiset.mem_toFinset,
        Polynomial.mem_roots (s1329FibreQuadratic_monic S1906W x).ne_zero]
      exact (s1329FibreQuadratic_eval_iff S1906W x y).mpr hns.1
    rw [s1329DivisionCandidates_mem]
    right
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, by
      simp only [s1329DivisionPoint, WeierstrassCurve.Affine.Point.mk]⟩

/-- Every candidate of the division locus is either zero or a nonzero point at
which psi_l vanishes. -/
theorem S1906Candidates_spec (l : PrimeGeFive) :
    ∀ P ∈ s1329DivisionCandidates S1906W l.value,
      P = 0 ∨ (P ≠ 0 ∧
        S1906W.evalDivisionPolynomialAtPoint (l.value : ℤ) P = 0) := by
  classical
  intro P hP
  rw [s1329DivisionCandidates_mem] at hP
  rcases hP with rfl | ⟨p, rfl⟩
  · exact Or.inl rfl
  · right
    have hEq : S1906W.Equation p.1.1 p.2.1 :=
      s1329Equation_of_mem_fibre_roots S1906W p.2.2
    have hns : S1906W.Nonsingular p.1.1 p.2.1 :=
      WeierstrassCurve.Affine.equation_iff_nonsingular.mp hEq
    constructor
    · simp only [s1329DivisionPoint, WeierstrassCurve.Affine.Point.mk]
      exact WeierstrassCurve.Affine.Point.some_ne_zero hns
    · simp only [s1329DivisionPoint, WeierstrassCurve.Affine.Point.mk]
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        S1906W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hEq (S1906_not_even l)]
      exact s1329PreΨ_eval_of_mem_roots S1906W (S1906_preΨ_ne_zero l) p.1.2

/-- The explicit division locus has at most l ^ 2 elements. -/
theorem S1906Candidates_card_le_sq (l : PrimeGeFive) :
    (s1329DivisionCandidates S1906W l.value).card ≤ l.value ^ 2 := by
  classical
  exact WeierstrassCurve.card_le_of_prime_divisionLocus_with_zero
    (W := S1906W) (p := l.value) l.prime
    (by have := l.ge_five; omega) (S1906_l_ne_zero l)
    (s1329DivisionCandidates S1906W l.value) (S1906Candidates_spec l)

/-- **Detection alone closes the upper half: |E'[l]| <= l ^ 2.** -/
theorem S1906NatCard_le_sq_of_detection (l : PrimeGeFive)
    (hdet : S1906Detection l) :
    Nat.card (S1720Curve.LTorsion l) ≤ l.value ^ 2 := by
  classical
  have hsub : (AddSubgroup.torsionBy S1906W.Point (l.value : ℤ) :
        Set S1906W.Point) ⊆
      ↑(s1329DivisionCandidates S1906W l.value) := by
    intro P hP
    exact S1906TorsionAffine_mem_candidates l hdet P hP
  have hfin : ((s1329DivisionCandidates S1906W l.value : Finset S1906W.Point) :
      Set S1906W.Point).Finite := Finset.finite_toSet _
  have hcard : Nat.card (AddSubgroup.torsionBy S1906W.Point (l.value : ℤ)) ≤
      (s1329DivisionCandidates S1906W l.value).card := by
    calc Nat.card (AddSubgroup.torsionBy S1906W.Point (l.value : ℤ))
        = (AddSubgroup.torsionBy S1906W.Point (l.value : ℤ) :
            Set S1906W.Point).ncard := rfl
      _ ≤ ((s1329DivisionCandidates S1906W l.value : Finset S1906W.Point) :
            Set S1906W.Point).ncard := Set.ncard_le_ncard hsub hfin
      _ = (s1329DivisionCandidates S1906W l.value).card := by
        rw [Set.ncard_coe_finset]
  rw [S1906NatCard_LTorsion_eq_affine l]
  exact hcard.trans (S1906Candidates_card_le_sq l)

/-- **Detection alone also makes the actual l-torsion finite.** -/
theorem S1906Finite_of_detection (l : PrimeGeFive)
    (hdet : S1906Detection l) : Finite (S1720Curve.LTorsion l) := by
  classical
  have hsub : (AddSubgroup.torsionBy S1906W.Point (l.value : ℤ) :
        Set S1906W.Point) ⊆
      ↑(s1329DivisionCandidates S1906W l.value) := by
    intro P hP
    exact S1906TorsionAffine_mem_candidates l hdet P hP
  have hfinAff : Finite (AddSubgroup.torsionBy S1906W.Point (l.value : ℤ)) :=
    (Finset.finite_toSet (s1329DivisionCandidates S1906W l.value)).subset hsub
  exact Finite.of_equiv _ (S1906TorsionEquiv l).symm

/-- The detection statement is exactly the first half of the group-law
criterion; the reverse detection is the second half. -/
theorem S1906Detection_iff (l : PrimeGeFive) :
    S1906Detection l ↔
      ∀ P : S1906W.Point, (l.value : ℤ) • P = 0 →
        S1906W.evalDivisionPolynomialAtPoint (l.value : ℤ) P = 0 :=
  Iff.rfl


/-! ## 5. The exact first missing statement and its division-polynomial
decomposition -/

/-- The exact target-level missing statement: the actual E'[l] has l ^ 2
elements.  This is *equivalent* to the basis gap, not a strengthening of it. -/
def S1906ExactFirstMissing (l : PrimeGeFive) : Prop :=
  Nat.card (S1720Curve.LTorsion l) = l.value ^ 2

/-- The exact first missing statement is literally the rank-two basis gap. -/
theorem S1906ExactFirstMissing_iff_basisGap (l : PrimeGeFive) :
    S1906ExactFirstMissing l ↔ S1725RankTwoBasisGap l :=
  (S1906RankTwoBasisGap_iff_natCard l).symm

/-- The three classical division-polynomial inputs used by the standard proof
of the cardinality.  The first is the coordinate formula x([n]P) = Phi_n/psi_n^2
for n >= 4, which is the explicit Mathlib gap recorded by S1361. -/
def S1906DivisionPolynomialInputs (l : PrimeGeFive) : Prop :=
  s1361XCoordinateFormula S1906W (l.value : ℤ) ∧
    S1906ZeroCriterion l ∧ S1906RootCount l

/-- The three division-polynomial inputs imply the exact first missing
statement. -/
theorem S1906ExactFirstMissing_of_divisionPolynomialInputs (l : PrimeGeFive)
    (h : S1906DivisionPolynomialInputs l) : S1906ExactFirstMissing l :=
  (S1906RankTwoBasisGap_iff_natCard l).mp
    (S1906BasisGap_of_xCoordinateFormula_zeroCriterion_rootCount
      l h.1 h.2.1 h.2.2)

/-- The forward detection half follows from the missing x-coordinate formula. -/
theorem S1906Detection_of_xCoordinateFormula (l : PrimeGeFive)
    (hX : s1361XCoordinateFormula S1906W (l.value : ℤ)) :
    S1906Detection l :=
  s1361Detection_of_xCoordinateFormula S1906W hX

/-- The group-law criterion is the conjunction of its two halves. -/
theorem S1906Criterion_iff_detection_zero (l : PrimeGeFive) :
    S1906Criterion l ↔ S1906Detection l ∧ S1906ZeroCriterion l :=
  S1906Criterion_iff l

/-- Detection alone gives the upper bound l ^ 2.  Hence, on the
division-polynomial route, only the lower bound (equivalently, under the
criterion, the full root count of prePsi_l) remains missing. -/
theorem S1906UpperBound_of_detection (l : PrimeGeFive)
    (hdet : S1906Detection l) :
    Nat.card (S1720Curve.LTorsion l) ≤ l.value ^ 2 :=
  S1906NatCard_le_sq_of_detection l hdet

/-- The missing lower bound is exactly the positive part of the cardinality
identity: if the cardinality is at least l ^ 2 then detection gives equality. -/
theorem S1906NatCard_eq_sq_of_detection_of_ge (l : PrimeGeFive)
    (hdet : S1906Detection l)
    (hge : l.value ^ 2 ≤ Nat.card (S1720Curve.LTorsion l)) :
    S1906ExactFirstMissing l :=
  le_antisymm (S1906NatCard_le_sq_of_detection l hdet) hge

/-! ## 6. Axiom footprint -/

#print axioms S1906NatCard_LTorsion_eq_affine
#print axioms S1906NatCard_fin_two
#print axioms S1906NatCard_eq_sq_of_basis
#print axioms S1906Finite_of_natCard
#print axioms S1906Basis_of_natCard
#print axioms S1906RankTwoBasisGap_iff_natCard
#print axioms S1906RankTwoBasisGap_iff_finrank
#print axioms S1906Finite_of_basisGap
#print axioms S1906ModuleFinite_of_basisGap
#print axioms S1906FiniteFreeRankTwo_of_basisGap
#print axioms S1906FiniteFreeRankTwo_of_natCard
#print axioms S1906Criterion_iff
#print axioms S1906_two_ne_zero
#print axioms S1906_l_ne_zero
#print axioms S1906_not_even
#print axioms S1906_preΨ_ne_zero
#print axioms S1906NoTwoTorsionRoots_of_criterion
#print axioms S1906NatCard_eq
#print axioms S1906NatCard_eq_sq_iff_rootCount
#print axioms S1906RankTwoBasisGap_iff_rootCount_of_criterion
#print axioms S1906BasisGap_of_detection_zeroCriterion_rootCount
#print axioms S1906BasisGap_of_xCoordinateFormula_zeroCriterion_rootCount
#print axioms S1906TorsionCardinality_iff_basisGap
#print axioms S1906TorsionAffine_mem_candidates
#print axioms S1906Candidates_spec
#print axioms S1906Candidates_card_le_sq
#print axioms S1906NatCard_le_sq_of_detection
#print axioms S1906Finite_of_detection
#print axioms S1906ExactFirstMissing_iff_basisGap
#print axioms S1906ExactFirstMissing_of_divisionPolynomialInputs
#print axioms S1906Detection_of_xCoordinateFormula
#print axioms S1906UpperBound_of_detection
#print axioms S1906NatCard_eq_sq_of_detection_of_ge


/-! ## 7. The root count from separability of prePsi_l -/

/-- Separability of the odd l-division polynomial over the actual closure. -/
def S1906Separability (l : PrimeGeFive) : Prop :=
  (S1906W.preΨ (l.value : ℤ)).Separable

/-- **Separability gives the full root count.**  Over the algebraically closed
field K, prePsi_l splits; if it is separable then its roots are pairwise
distinct, so the root multiset has cardinality its degree (l ^ 2 - 1) / 2. -/
theorem S1906RootCount_of_separable (l : PrimeGeFive)
    (hsep : S1906Separability l) : S1906RootCount l := by
  have hnd : (S1906W.preΨ (l.value : ℤ)).roots.Nodup :=
    Polynomial.nodup_roots hsep
  have hsplit : (S1906W.preΨ (l.value : ℤ)).Splits :=
    IsAlgClosed.splits _
  have hcard : (S1906W.preΨ (l.value : ℤ)).roots.card =
      (S1906W.preΨ (l.value : ℤ)).natDegree :=
    hsplit.natDegree_eq_card_roots.symm
  have hpre : ((l.value : ℤ) : S1906K) ≠ 0 := by
    simpa using S1906_l_ne_zero l
  change (s1329RootFinset S1906W l.value).card = (l.value ^ 2 - 1) / 2
  rw [s1329RootFinset, Multiset.toFinset_card_of_nodup hnd, hcard,
    WeierstrassCurve.natDegree_preΨ (W := S1906W) (n := (l.value : ℤ)) hpre,
    if_neg (S1906_not_even l)]
  simp

/-- The tree's generic separability input S1366GenericOddPreΨSeparableInput
(S1366, S1420) specialises to the actual curve and gives the root count. -/
theorem S1906RootCount_of_genericPreΨSeparable
    (h : S1366GenericOddPreΨSeparableInput) (l : PrimeGeFive) :
    S1906RootCount l :=
  S1906RootCount_of_separable l
    (h S1906K S1906W (l.value : ℤ) (S1906_not_even l) (by
      exact_mod_cast l.prime.ne_zero))

/-- The three genuinely classical inputs of the division-polynomial route,
with separability in place of the root count. -/
def S1906AlgebraicInputs (l : PrimeGeFive) : Prop :=
  s1361XCoordinateFormula S1906W (l.value : ℤ) ∧
    S1906ZeroCriterion l ∧ S1906Separability l

/-- **The exact division-polynomial closure.**  The Mathlib-missing
x-coordinate formula, the Mathlib-missing reverse detection, and the
S1366/S1420 separability input imply the actual rank-two basis gap. -/
theorem S1906BasisGap_of_xCoordinateFormula_zeroCriterion_separable
    (l : PrimeGeFive)
    (hX : s1361XCoordinateFormula S1906W (l.value : ℤ))
    (hzero : S1906ZeroCriterion l) (hsep : S1906Separability l) :
    S1725RankTwoBasisGap l :=
  S1906BasisGap_of_xCoordinateFormula_zeroCriterion_rootCount l hX hzero
    (S1906RootCount_of_separable l hsep)

/-- The same closure from the tree's generic separability input. -/
theorem S1906BasisGap_of_xCoordinateFormula_zeroCriterion_genericSeparable
    (hsep : S1366GenericOddPreΨSeparableInput) (l : PrimeGeFive)
    (hX : s1361XCoordinateFormula S1906W (l.value : ℤ))
    (hzero : S1906ZeroCriterion l) : S1725RankTwoBasisGap l :=
  S1906BasisGap_of_xCoordinateFormula_zeroCriterion_separable l hX hzero
    (hsep S1906K S1906W (l.value : ℤ) (S1906_not_even l) (by
      exact_mod_cast l.prime.ne_zero))

/-- The exact first missing statement in the algebraic-input form: the
conjunction of the x-coordinate formula, reverse detection and separability. -/
def S1906ExactFirstMissingAlgebraic (l : PrimeGeFive) : Prop :=
  S1906AlgebraicInputs l

/-- The algebraic-input form implies the exact first missing cardinality. -/
theorem S1906ExactFirstMissing_of_algebraicInputs (l : PrimeGeFive)
    (h : S1906AlgebraicInputs l) : S1906ExactFirstMissing l :=
  (S1906RankTwoBasisGap_iff_natCard l).mp
    (S1906BasisGap_of_xCoordinateFormula_zeroCriterion_separable
      l h.1 h.2.1 h.2.2)

#print axioms S1906RootCount_of_separable
#print axioms S1906RootCount_of_genericPreΨSeparable
#print axioms S1906BasisGap_of_xCoordinateFormula_zeroCriterion_separable
#print axioms S1906BasisGap_of_xCoordinateFormula_zeroCriterion_genericSeparable
#print axioms S1906ExactFirstMissing_of_algebraicInputs

end LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
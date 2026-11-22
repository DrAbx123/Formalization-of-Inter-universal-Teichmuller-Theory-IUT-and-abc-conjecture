import tmp.sheaf.xif.paper.S1550TatePointComparisonFromClosureActual
import tmp.sheaf.xif.paper.S1444ReportAKPlaceQActual
import tmp.sheaf.xif.paper.S2190RootSourceConditionsActual
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Int.GCD
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

/-!
# S2223: the Tate-uniformization bridge from the actual clause-(c) data

This file is deliberately split into three layers.

## 1. The uniformization is actual

S1550 constructs the K-side Tate point comparison
TatePointComparison (kSideCurve T) (sectionKPlace T b) (sectionQ T b), and hence
the K-side TateCurveComparison.  The old claim that "the Tate uniformization
bridge is not in the tree" is therefore no longer true at the comparison level;
it is reproduced below as tateUniformization_available.

## 2. What the root extraction really needs

Given a completion element q and a base unit x with
x ^ n = q ^ m and gcd (n, m) = 1, the n-th root of q is constructed
unconditionally by Bezout (sqrt_of_odd_zpow, lthRoot_of_coprime_zpow).
This is the Kummer part of the paper's argument and is proved here.

The remaining Tate content is the torsion parameter:
a fixed n-torsion point P of the K-side curve over the completion
together with a base unit x : K_v-units representing the class
pointEquiv^{-1} P and with the exponent relation x^n = q^m whose m is
odd (for n = 2) or coprime to l (for n = l).

The clause-(c) data supply the torsion points over the algebraic closure
(torsion_basis for l, and torsion23_rational for the 2-torsion points,
via the explicit two-torsion construction below).  What they do not supply is
the descent of the Tate class to a unit of the completion.  That descent is
recorded as the precise missing parameter
S2223TwoTorsionTateParameter / S2223LTorsionTateParameter.

## 3. No A/B axiom

S2190QSquareSource and S2190QLthPowerSource are not assumed anywhere.
They are derived from the exact Tate parameters above by the Kummer lemmas.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2223TateBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual
open WeierstrassCurve
open Polynomial

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The actual K-side Tate uniformization -/

/-- S1550's K-side Tate point comparison, at the paper's section K-place. -/
noncomputable def s2223TatePointComparison :
    TatePointComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b) :=
  tatePointComparison (T := T) (b := b)

/-- The K-side TateCurveComparison is available: field canonicalIsElliptic,
coordinateChange, realizesCurve, and the point comparison all exist. -/
noncomputable def s2223TateCurveComparison :
    TateCurveComparison (kSideCurve (T := T)) (sectionKPlace T b) (sectionQ T b) :=
  tateCurveComparison (T := T) (b := b)

/-- The Tate-uniformization bridge exists. -/
theorem tateUniformization_available :
    Nonempty (TateCurveComparison (kSideCurve (T := T))
      (sectionKPlace T b) (sectionQ T b)) :=
  ⟨s2223TateCurveComparison T b⟩

/-! ## 2. Kummer extraction from a base unit -/

/-- If x ^ 2 = q ^ m with m odd, then q is a square. -/
theorem sqrt_of_odd_zpow {K : Type u} [Field K] (q : K) (hq : q ≠ 0)
    (x : Kˣ) (m : ℤ) (hx : (x : K) ^ 2 = q ^ m) (hm : Odd m) :
    ∃ s : K, s ^ 2 = q := by
  obtain ⟨k, hk⟩ := hm
  have hqm : q ^ m = q * (q ^ k) ^ 2 := by
    rw [hk]
    rw [show (2 : ℤ) * k + 1 = 1 + k * 2 by ring]
    rw [zpow_add₀ hq]
    rw [show (q ^ k) ^ 2 = q ^ (k * 2) by
      rw [← zpow_natCast, ← zpow_mul]
      norm_num]
    rw [zpow_one, mul_comm]
  refine ⟨(x : K) / q ^ k, ?_⟩
  rw [div_pow, hx, hqm]
  field_simp [hq]

/-- If x ^ l = q ^ m and gcd (l, m) = 1, then q is an l-th power. -/
theorem lthRoot_of_coprime_zpow {K : Type u} [Field K] (l : Nat) (q : K) (hq : q ≠ 0)
    (x : Kˣ) (m : ℤ) (hx : (x : K) ^ l = q ^ m)
    (hcop : Nat.Coprime l m.natAbs) :
    ∃ s : K, s ^ l = q := by
  have hgcd : Int.gcd (l : ℤ) m = 1 := by
    rw [Int.gcd_def]
    have h : Nat.gcd l m.natAbs = 1 := hcop.gcd_eq_one
    simpa [Int.natAbs_natCast] using h
  let a : ℤ := Int.gcdA (l : ℤ) m
  let b : ℤ := Int.gcdB (l : ℤ) m
  have hbez : (1 : ℤ) = (l : ℤ) * a + m * b := by
    have h := Int.gcd_eq_gcd_ab (l : ℤ) m
    rw [hgcd] at h
    simpa [a, b] using h
  have hx' : (x : K) ^ (l : ℤ) = q ^ m := by
    rw [zpow_natCast]
    exact hx
  refine ⟨q ^ a * (x : K) ^ b, ?_⟩
  rw [mul_pow]
  have h1 : (q ^ a) ^ l = q ^ (a * (l : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
  have h2 : ((x : K) ^ b) ^ l = q ^ (m * b) := by
    rw [← zpow_natCast, ← zpow_mul]
    rw [show b * (l : ℤ) = (l : ℤ) * b by ring]
    rw [zpow_mul, hx']
    rw [← zpow_mul]
  rw [h1, h2, ← zpow_add₀ hq]
  rw [show a * (l : ℤ) + m * b = 1 by linarith [hbez]]
  rw [zpow_one]

/-! ## 3. Explicit two-torsion points over the algebraic closure -/

variable {F : Type u} [Field F] [CharZero F]

noncomputable local instance s2223DecEqAlgClosure : DecidableEq (AlgebraicClosure F) :=
  Classical.decEq _

theorem twoTorsionPolynomial_baseChange (W : WeierstrassCurve F) (L : Type*) [Field L]
    [Algebra F L] :
    (W.baseChange L).twoTorsionPolynomial =
      (W.twoTorsionPolynomial).map (algebraMap F L) := by
  ext <;>
    simp only [Cubic.map, WeierstrassCurve.twoTorsionPolynomial, WeierstrassCurve.baseChange,
      WeierstrassCurve.map, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      map_ofNat, map_add, map_mul, map_pow]

theorem twoTorsionPoint_of_root (W : WeierstrassCurve F) [W.IsElliptic]
    (L : Type*) [Field L] [CharZero L] [Algebra F L] [DecidableEq L] (x : L)
    (hx : (W.baseChange L).twoTorsionPolynomial.toPoly.eval x = 0) :
    ∃ (y : L) (h : (W.baseChange L).toAffine.Nonsingular x y),
      (2 : Nat) • (WeierstrassCurve.Affine.Point.some x y h) = 0 := by
  let y : L := -((W.baseChange L).a₁ * x + (W.baseChange L).a₃) / 2
  have heq : (W.baseChange L).toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [WeierstrassCurve.twoTorsionPolynomial] at hx
    simp only [Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] at hx
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hx
    change y ^ 2 + (W.baseChange L).a₁ * x * y + (W.baseChange L).a₃ * y =
      x ^ 3 + (W.baseChange L).a₂ * x ^ 2 + (W.baseChange L).a₄ * x + (W.baseChange L).a₆
    subst y
    field_simp
    ring_nf at hx
    ring_nf
    linear_combination (-1 : L) * hx
  have hΔ : (W.baseChange L).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact (map_ne_zero (algebraMap F L)).mpr (W.isUnit_Δ.ne_zero)
  have hns : (W.baseChange L).toAffine.Nonsingular x y :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (W := (W.baseChange L)) hΔ).mp heq
  refine ⟨y, hns, ?_⟩
  have hdiv : (W.baseChange L).evalDivisionPolynomial x y 2 = 0 := by
    rw [WeierstrassCurve.evalDivisionPolynomial_two]
    change 2 * y + (W.baseChange L).a₁ * x + (W.baseChange L).a₃ = 0
    subst y
    field_simp
    ring
  have hy : y = (W.baseChange L).toAffine.negY x y :=
    (WeierstrassCurve.evalDivisionPolynomial_two_eq_zero_iff_negY
      (W := (W.baseChange L))).mp hdiv
  rw [show (2 : Nat) • (WeierstrassCurve.Affine.Point.some x y hns) =
      WeierstrassCurve.Affine.Point.some x y hns + WeierstrassCurve.Affine.Point.some x y hns by
    rw [two_nsmul]]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy

/-- Three distinct nonzero two-torsion points over the algebraic closure. -/
theorem exists_three_twoTorsionPoints (W : WeierstrassCurve F) [W.IsElliptic] :
    ∃ (x₁ x₂ x₃ : AlgebraicClosure F)
      (y₁ y₂ y₃ : AlgebraicClosure F)
      (h₁ : (W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x₁ y₁)
      (h₂ : (W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x₂ y₂)
      (h₃ : (W.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x₃ y₃),
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧
      (2 : Nat) • (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0 ∧
      (2 : Nat) • (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0 ∧
      (2 : Nat) • (WeierstrassCurve.Affine.Point.some x₃ y₃ h₃) = 0 := by
  let P := W.twoTorsionPolynomial
  have ha : P.a ≠ 0 := by
    simp [P, WeierstrassCurve.twoTorsionPolynomial]
  have hsplit : (P.toPoly.map (algebraMap F (AlgebraicClosure F))).Splits :=
    IsAlgClosed.splits _
  obtain ⟨x₁, x₂, x₃, hroots⟩ :=
    (Cubic.splits_iff_roots_eq_three (P := P)
      (φ := algebraMap F (AlgebraicClosure F)) ha).mp hsplit
  have hdiscr : P.discr ≠ 0 := by
    change W.twoTorsionPolynomial.discr ≠ 0
    rw [WeierstrassCurve.twoTorsionPolynomial_discr]
    exact mul_ne_zero (by norm_num) (W.isUnit_Δ.ne_zero)
  have hne := (Cubic.discr_ne_zero_iff_roots_ne (P := P)
    (φ := algebraMap F (AlgebraicClosure F)) ha hroots).mp hdiscr
  have hmap_poly : (P.map (algebraMap F (AlgebraicClosure F))).toPoly ≠ 0 :=
    Cubic.ne_zero_of_a_ne_zero (by
      have h4 : (P.map (algebraMap F (AlgebraicClosure F))).a = 4 := by
        simp only [P, Cubic.map, WeierstrassCurve.twoTorsionPolynomial]
        exact map_ofNat (algebraMap F (AlgebraicClosure F)) 4
      rw [h4]; norm_num)
  have root_eval (x : AlgebraicClosure F)
      (hxmem : x ∈ (P.map (algebraMap F (AlgebraicClosure F))).roots) :
      (W.baseChange (AlgebraicClosure F)).twoTorsionPolynomial.toPoly.eval x = 0 := by
    have hx0 : (P.map (algebraMap F (AlgebraicClosure F))).a * x ^ 3 +
        (P.map (algebraMap F (AlgebraicClosure F))).b * x ^ 2 +
        (P.map (algebraMap F (AlgebraicClosure F))).c * x +
        (P.map (algebraMap F (AlgebraicClosure F))).d = 0 :=
      (Cubic.mem_roots_iff (P := P.map (algebraMap F (AlgebraicClosure F)))
        hmap_poly x).mp hxmem
    simpa [twoTorsionPolynomial_baseChange W (AlgebraicClosure F), Cubic.toPoly,
      Cubic.map, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X] using hx0
  have hx₁mem : x₁ ∈ (P.map (algebraMap F (AlgebraicClosure F))).roots := by rw [hroots]; simp
  have hx₂mem : x₂ ∈ (P.map (algebraMap F (AlgebraicClosure F))).roots := by rw [hroots]; simp
  have hx₃mem : x₃ ∈ (P.map (algebraMap F (AlgebraicClosure F))).roots := by rw [hroots]; simp
  obtain ⟨y₁, h₁, hp₁⟩ :=
    twoTorsionPoint_of_root W (AlgebraicClosure F) x₁ (root_eval x₁ hx₁mem)
  obtain ⟨y₂, h₂, hp₂⟩ :=
    twoTorsionPoint_of_root W (AlgebraicClosure F) x₂ (root_eval x₂ hx₂mem)
  obtain ⟨y₃, h₃, hp₃⟩ :=
    twoTorsionPoint_of_root W (AlgebraicClosure F) x₃ (root_eval x₃ hx₃mem)
  exact ⟨x₁, x₂, x₃, y₁, y₂, y₃, h₁, h₂, h₃,
    hne.1, hne.2.1, hne.2.2, hp₁, hp₂, hp₃⟩

/-! ## 4. The exact missing Tate parameters -/

/-- The exact two-torsion Tate parameter at the paper's section K-place. -/
structure S2223TwoTorsionTateParameter where
  P : SideKPoint T b
  point_two_torsion : (2 : Nat) • P = 0
  x : (Kv T b)ˣ
  m : ℤ
  class_eq : pointEquiv T b (QuotientGroup.mk
    (Units.map (algebraMap (Kv T b) (LK T b)).toMonoidHom x) : DeckK T b) =
      Multiplicative.ofAdd P
  pow_eq : (x : Kv T b) ^ 2 = (sectionQ T b).q ^ m
  m_odd : Odd m

/-- The exact l-torsion Tate parameter at the paper's section K-place. -/
structure S2223LTorsionTateParameter where
  P : SideKPoint T b
  point_l_torsion : l.value • P = 0
  x : (Kv T b)ˣ
  m : ℤ
  class_eq : pointEquiv T b (QuotientGroup.mk
    (Units.map (algebraMap (Kv T b) (LK T b)).toMonoidHom x) : DeckK T b) =
      Multiplicative.ofAdd P
  pow_eq : (x : Kv T b) ^ l.value = (sectionQ T b).q ^ m
  m_coprime : Nat.Coprime l.value m.natAbs

/-- The two-torsion Tate parameter gives the square source condition A. -/
theorem S2190QSquareSource_of_twoTorsionTateParameter
    (h : S2223TwoTorsionTateParameter T b) : S2190QSquareSource T b := by
  obtain ⟨P, hP2, x, m, hclass, hpow, hm⟩ := h
  obtain ⟨s, hs⟩ := sqrt_of_odd_zpow (sectionQ T b).q (sectionQ T b).q_ne_zero x m hpow hm
  exact ⟨s, hs⟩

/-- The l-torsion Tate parameter gives the l-th power source condition B. -/
theorem S2190QLthPowerSource_of_lTorsionTateParameter
    (h : S2223LTorsionTateParameter T b) : S2190QLthPowerSource T b := by
  obtain ⟨P, hPl, x, m, hclass, hpow, hcop⟩ := h
  obtain ⟨s, hs⟩ := lthRoot_of_coprime_zpow l.value (sectionQ T b).q
    (sectionQ T b).q_ne_zero x m hpow hcop
  exact ⟨s, hs⟩

/-- The two exact Tate parameters together give the two S2190 source conditions
(without assuming either source condition as an axiom). -/
theorem halfRootSource_of_tateParameters
    (h2 : S2223TwoTorsionTateParameter T b)
    (hl : S2223LTorsionTateParameter T b) :
    S2190HalfRootSource T b :=
  ⟨S2190QSquareSource_of_twoTorsionTateParameter T b h2,
    S2190QLthPowerSource_of_lTorsionTateParameter T b hl⟩

/-! ## 5. What is actually supplied by clause (c) -/

/-- Clause (c)'s six-torsion rationality is available and is what makes the
explicit two-torsion points rational over F. -/
theorem actual_torsion23_data :
    PuncturedEllipticCurve.Torsion23Rational T.arithmetic.curve :=
  T.clauseC.torsion23_rational

/-- Clause (c)'s actual l-torsion basis. -/
noncomputable def actual_lTorsionBasis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] T.arithmetic.curve.LTorsion l :=
  T.clauseC.torsion_basis

/-- The actual kernel-field identification of clause (c). -/
noncomputable def actual_kernelFieldIdentification :
    T.arithmetic.K ≃ₐ[T.arithmetic.F]
      T.arithmetic.curve.galoisLTorsionKernelField l T.clauseC.torsion_basis :=
  T.clauseC.kernel_field_identification

/-- The exact first missing, stated in one line: the base-unit descent of the
two Tate torsion classes.  This is the only datum not supplied by the
uniformization comparison and the clause-(c) torsion points. -/
def S2223TateBaseUnitDescent : Prop :=
  Nonempty (S2223TwoTorsionTateParameter T b) ∧
    Nonempty (S2223LTorsionTateParameter T b)

/-- With the exact Tate torsion parameters, both S2190 source conditions hold. -/
theorem halfRootSource_of_tateBaseUnitDescent
    (h : S2223TateBaseUnitDescent T b) : S2190HalfRootSource T b := by
  obtain ⟨⟨h2⟩, ⟨hl⟩⟩ := h
  exact halfRootSource_of_tateParameters T b h2 hl

/-! ## 6. Status and exact missing

Proved unconditionally here:

* tateUniformization_available: the K-side TateCurveComparison exists (S1550);
* sqrt_of_odd_zpow and lthRoot_of_coprime_zpow: the Kummer root extraction;
* twoTorsionPoint_of_root and exists_three_twoTorsionPoints: the three nonzero
  two-torsion points over the algebraic closure.

Proved conditionally on the exact Tate torsion parameters:

* S2190QSquareSource_of_twoTorsionTateParameter;
* S2190QLthPowerSource_of_lTorsionTateParameter.

The exact first missing is S2223TateBaseUnitDescent, i.e. the two structures
S2223TwoTorsionTateParameter and S2223LTorsionTateParameter.  Their missing
field is the base unit x : K_v-units together with the class equality and the
odd / coprime exponent.  The uniformization comparison and the clause-(c)
torsion points are already actual; the completion-unit descent is not.

Consequently A/B are not claimed unconditionally in this file. -/

/-! ## 7. Axiom audit -/

#print axioms tateUniformization_available
#print axioms sqrt_of_odd_zpow
#print axioms lthRoot_of_coprime_zpow
#print axioms twoTorsionPoint_of_root
#print axioms exists_three_twoTorsionPoints
#print axioms S2190QSquareSource_of_twoTorsionTateParameter
#print axioms S2190QLthPowerSource_of_lTorsionTateParameter
#print axioms halfRootSource_of_tateParameters
#print axioms halfRootSource_of_tateBaseUnitDescent

end LeanFormal.IUT.XiFPaper.S2223TateBridgeActual

end

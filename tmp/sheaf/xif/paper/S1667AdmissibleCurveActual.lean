import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import tmp.sheaf.xif.paper.S1637D5TorsionClauseActual

/-!
# S1667: an actual admissible curve for paper D5 condition (b)

## What this file does

The Gaussian input of S1280 is the curve y^2 + x*y = x^3 + 5 over Q(i).
S1637 records that its 2-torsion is not rational over Q(i), so the paper
condition (b) Torsion23Rational is empty for that curve, and that (b) cannot
be replaced by the independence of 6- and l-torsion.

This file constructs a different, faithful concrete input over Q:

  E : y^2 = x^3 + (61/64) x^2 - (125/64) x = x (x - 1) (x + 125/64),

i.e. the Legendre curve with parameter lambda = -125/64.

The file proves, with no axioms and no sorry:

* E is an elliptic curve over Q;
* the 2-division polynomial evaluates as 4 x (x - 1) (x + 125/64), so all
  three 2-torsion points (0,0), (1,0), (-125/64,0) are rational over Q;
* the 3-division polynomial evaluates as
  (1/256) (x - 25/16) (768 x^3 + 2176 x^2 + 400 x + 625),
  so P = (25/16, 225/128) is a rational 3-torsion point;
* the residual cubic 768 x^3 + 2176 x^2 + 400 x + 625 has no rational root
  (proved modulo 13), so the six remaining 3-torsion points are genuinely
  non-rational and a faithful condition (b) must pass to a number field;
* Q = (-5/4, 45/32) is a rational 6-torsion point, with
  2 Q = -P, 3 Q = (0,0), 6 Q = 0, addOrderOf Q = 6, and P has order 3;
* the reduction arithmetic of the split-multiplicative place is recorded:
  c_4 = 27721/256 is a 5-adic unit and Delta = 558140625/1048576 has
  v_5 = 6 (5^6 divides the numerator, 5^7 does not).

The exact remaining construction for a faithful D5 condition (b) is recorded
as S1667Torsion23Realization: a number field F, an algebra Q -> F, and a
proof of Torsion23Rational for the base-changed curve.  Mathematically the
candidate is the 3-division field F = Q(E[3]), the splitting field of the
residual cubic 768 X^3 + 2176 X^2 + 400 X + 625 (degree 6, Galois group
S_3); its discriminant is -2^16 * 3^5 * 5^4 * 7^4, whose square class is
-3, so the quadratic subfield of F is Q(sqrt(-3)) = Q(zeta_3), exactly the
determinant requirement of the Weil pairing.  Over F all 8 three-torsion
points and hence all 36 six-torsion points are rational.  Base-changing E to F preserves the multiplicative reduction
at the odd prime 5: the model is integral at 5, c_4 = 27721/256 is a 5-adic
unit and v_5(Delta) = 6, and the split tangent polynomial is X^2 + 1 over
F_5, which splits.  The Lean file records the 5-adic valuation arithmetic;
the local-field split-multiplicative predicate itself is the remaining
reduction-side construction.  Constructing this degree-6 field and its
torsion coordinates in Lean is the precise first missing construction; it is
not faked here.

## Why the base field must be larger than Q and Q(i)

If E[6] is rational over a field F, the Weil pairing makes the values of
e_6 rational over F, hence mu_6 <= F^*; so Q(zeta_6) = Q(sqrt(-3)) is
a subfield of F.  In particular neither Q nor Q(i) can host a curve with
Torsion23Rational.  Moreover Q(sqrt(-3)) has degree 2 and full torsion
(Z/6)^2 is impossible over a quadratic field (Kenku-Momose); thus a faithful
input needs a number field of degree at least 3, and the candidate above has
degree 6.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial
open scoped Polynomial.Bivariate
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1637D5TorsionClauseActual

/-! ## 1. The concrete curve -/

/-- The admissible candidate: the Legendre curve y^2 = x(x-1)(x + 125/64),
written in general Weierstrass form with
a_2 = 61/64, a_4 = -125/64, a_1 = a_3 = a_6 = 0. -/
def S1667Curve : WeierstrassCurve ℚ :=
  WeierstrassCurve.mk 0 (61/64) 0 (-125/64) 0

@[simp] theorem S1667Curve_a₁ : S1667Curve.a₁ = 0 := rfl
@[simp] theorem S1667Curve_a₂ : S1667Curve.a₂ = (61/64 : ℚ) := rfl
@[simp] theorem S1667Curve_a₃ : S1667Curve.a₃ = 0 := rfl
@[simp] theorem S1667Curve_a₄ : S1667Curve.a₄ = (-125/64 : ℚ) := rfl
@[simp] theorem S1667Curve_a₆ : S1667Curve.a₆ = 0 := rfl

theorem S1667Curve_b₂ : S1667Curve.b₂ = (61/16 : ℚ) := by
  norm_num [S1667Curve, WeierstrassCurve.b₂]

theorem S1667Curve_b₄ : S1667Curve.b₄ = (-125/32 : ℚ) := by
  norm_num [S1667Curve, WeierstrassCurve.b₄]

theorem S1667Curve_b₆ : S1667Curve.b₆ = (0 : ℚ) := by
  norm_num [S1667Curve, WeierstrassCurve.b₆]

theorem S1667Curve_b₈ : S1667Curve.b₈ = (-15625/4096 : ℚ) := by
  norm_num [S1667Curve, WeierstrassCurve.b₈]

theorem S1667Curve_c₄ : S1667Curve.c₄ = (27721/256 : ℚ) := by
  norm_num [S1667Curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

theorem S1667Curve_Δ : S1667Curve.Δ = (558140625/1048576 : ℚ) := by
  norm_num [S1667Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem S1667Curve_Δ_ne_zero : S1667Curve.Δ ≠ 0 := by
  rw [S1667Curve_Δ]
  norm_num

theorem S1667Curve_isElliptic : S1667Curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr S1667Curve_Δ_ne_zero⟩

/-- The punctured curve used by the source clause (the puncture is the point at
infinity, an actual nonsingular projective point). -/
def S1667Punctured : PuncturedEllipticCurve ℚ where
  curve := S1667Curve
  isElliptic := S1667Curve_isElliptic
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

@[simp] theorem S1667Punctured_curve : S1667Punctured.curve = S1667Curve := rfl

/-! ## 2. Full rational 2-torsion -/

/-- The 2-division polynomial splits completely over Q (evaluated form). -/
theorem S1667_Ψ₂Sq_eval (x : ℚ) :
    S1667Curve.Ψ₂Sq.eval x = 4 * x * (x - 1) * (x + 125/64) := by
  rw [WeierstrassCurve.Ψ₂Sq]
  simp only [S1667Curve_b₂, S1667Curve_b₄, S1667Curve_b₆]
  simp
  ring

theorem S1667_Ψ₂Sq_eval_zero : S1667Curve.Ψ₂Sq.eval 0 = 0 := by
  rw [S1667_Ψ₂Sq_eval]; norm_num

theorem S1667_Ψ₂Sq_eval_one : S1667Curve.Ψ₂Sq.eval 1 = 0 := by
  rw [S1667_Ψ₂Sq_eval]; norm_num

theorem S1667_Ψ₂Sq_eval_lambda : S1667Curve.Ψ₂Sq.eval (-125/64) = 0 := by
  rw [S1667_Ψ₂Sq_eval]; norm_num

lemma S1667_nonsingular_zero : S1667Curve.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]; norm_num [S1667Curve]
  · norm_num [S1667Curve]

lemma S1667_nonsingular_one : S1667Curve.toAffine.Nonsingular 1 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]; norm_num [S1667Curve]
  · norm_num [S1667Curve]

lemma S1667_nonsingular_lambda : S1667Curve.toAffine.Nonsingular (-125/64) 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]; norm_num [S1667Curve]
  · norm_num [S1667Curve]

/-- The x = 0 two-torsion point. -/
def S1667T0 : S1667Curve.toAffine.Point :=
  Affine.Point.some (W' := S1667Curve.toAffine) 0 0 S1667_nonsingular_zero

/-- The x = 1 two-torsion point. -/
def S1667T1 : S1667Curve.toAffine.Point :=
  Affine.Point.some (W' := S1667Curve.toAffine) 1 0 S1667_nonsingular_one

/-- The x = -125/64 two-torsion point. -/
def S1667T2 : S1667Curve.toAffine.Point :=
  Affine.Point.some (W' := S1667Curve.toAffine) (-125/64) 0 S1667_nonsingular_lambda

/-- A point (x, 0) is two-torsion. -/
theorem S1667_two_nsmul_of_y_zero {x : ℚ}
    (hns : S1667Curve.toAffine.Nonsingular x 0) :
    (2 : ℤ) • (Affine.Point.some (W' := S1667Curve.toAffine) x 0 hns) = 0 := by
  rw [show (2 : ℤ) • (Affine.Point.some (W' := S1667Curve.toAffine) x 0 hns) =
      Affine.Point.some (W' := S1667Curve.toAffine) x 0 hns +
        Affine.Point.some (W' := S1667Curve.toAffine) x 0 hns by rw [two_zsmul]]
  apply Affine.Point.add_self_of_Y_eq
  norm_num [S1667Curve, WeierstrassCurve.Affine.negY]

theorem S1667T0_two : (2 : ℤ) • S1667T0 = 0 :=
  S1667_two_nsmul_of_y_zero _

theorem S1667T1_two : (2 : ℤ) • S1667T1 = 0 :=
  S1667_two_nsmul_of_y_zero _

theorem S1667T2_two : (2 : ℤ) • S1667T2 = 0 :=
  S1667_two_nsmul_of_y_zero _

theorem S1667T0_ne_zero : S1667T0 ≠ 0 :=
  Affine.Point.some_ne_zero S1667_nonsingular_zero

theorem S1667T1_ne_zero : S1667T1 ≠ 0 :=
  Affine.Point.some_ne_zero S1667_nonsingular_one

theorem S1667T2_ne_zero : S1667T2 ≠ 0 :=
  Affine.Point.some_ne_zero S1667_nonsingular_lambda

theorem S1667T0_ne_T1 : S1667T0 ≠ S1667T1 := by
  intro h
  have h' := Affine.Point.some.inj h
  norm_num at h'

theorem S1667T0_ne_T2 : S1667T0 ≠ S1667T2 := by
  intro h
  have h' := Affine.Point.some.inj h
  norm_num at h'

theorem S1667T1_ne_T2 : S1667T1 ≠ S1667T2 := by
  intro h
  have h' := Affine.Point.some.inj h
  norm_num at h'

/-- The exact roots of the 2-division polynomial: the full rational 2-torsion. -/
theorem S1667_two_division_roots (x : ℚ) :
    S1667Curve.Ψ₂Sq.eval x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -125/64 := by
  rw [S1667_Ψ₂Sq_eval]
  constructor
  · intro h
    have h' : x * (x - 1) * (x + 125/64) = 0 := by
      have h4 : (4 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp (by simpa using h)).resolve_left h4
    rcases mul_eq_zero.mp h' with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · left; linarith
      · right; left; linarith
    · right; right; linarith
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- The 2-torsion point x = 0 has order exactly two. -/
theorem S1667T0_order : addOrderOf S1667T0 = 2 := by
  rw [addOrderOf_eq_iff (by norm_num : 0 < 2)]
  constructor
  · exact S1667T0_two
  · intro m hm hpos
    interval_cases m
    · change S1667T0 ≠ 0
      exact S1667T0_ne_zero

/-! ## 3. The 3-division polynomial and a rational 3-torsion point -/

/-- The residual cubic of the 3-division polynomial; its roots are the
x-coordinates of the six non-rational 3-torsion points. -/
def S1667ResidualCubic : ℚ[X] :=
  768 * X ^ 3 + 2176 * X ^ 2 + 400 * X + 625

theorem S1667ResidualCubic_eval (x : ℚ) :
    S1667ResidualCubic.eval x = 768 * x ^ 3 + 2176 * x ^ 2 + 400 * x + 625 := by
  simp [S1667ResidualCubic]

local instance S1667FactPrimeThirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The residual cubic has no root modulo 13. -/
theorem S1667_residualCubic_noRootMod13 (r : ZMod 13) :
    768 * r ^ 3 + 2176 * r ^ 2 + 400 * r + 625 ≠ 0 := by
  revert r
  decide

/-- **The residual 3-division cubic has no rational root.**  Consequently the
three roots of the residual cubic, hence the x-coordinates of the six
non-rational 3-torsion points, are not rational over Q, and a faithful
condition (b) needs a genuine number-field extension. -/
theorem S1667ResidualCubic_no_rational_root :
    ¬ ∃ x : ℚ, S1667ResidualCubic.eval x = 0 := by
  rintro ⟨x, hx⟩
  rw [S1667ResidualCubic_eval] at hx
  set a : ℤ := x.num with ha
  set b : ℕ := x.den with hb
  have hb0 : b ≠ 0 := x.den_nz
  have hxq : (x : ℚ) = (a : ℚ) / (b : ℚ) := by
    rw [ha, hb, Rat.num_div_den]
  have hQ : 768 * (a : ℚ) ^ 3 + 2176 * (a : ℚ) ^ 2 * (b : ℚ) +
      400 * (a : ℚ) * (b : ℚ) ^ 2 + 625 * (b : ℚ) ^ 3 = 0 := by
    have h := hx
    rw [hxq] at h
    field_simp at h
    linear_combination h
  have hZ : 768 * a ^ 3 + 2176 * a ^ 2 * (b : ℤ) +
      400 * a * (b : ℤ) ^ 2 + 625 * (b : ℤ) ^ 3 = 0 := by
    exact_mod_cast hQ
  have h13 : 768 * (a : ZMod 13) ^ 3 + 2176 * (a : ZMod 13) ^ 2 * (b : ZMod 13) +
      400 * (a : ZMod 13) * (b : ZMod 13) ^ 2 + 625 * (b : ZMod 13) ^ 3 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod 13)) hZ
    push_cast at this
    simpa using this
  by_cases hb13 : (b : ZMod 13) = 0
  · have h13b : (13 : ℤ) ∣ (b : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (b : ℤ) 13).mp (by exact_mod_cast hb13)
    have hb13n : 13 ∣ b := Int.ofNat_dvd.mp h13b
    have h13' : (a : ZMod 13) ^ 3 = 0 := by
      have h := h13
      rw [hb13] at h
      have h768 : (768 : ZMod 13) = 1 := by decide
      simpa [h768] using h
    have ha0 : (a : ZMod 13) = 0 := by
      exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h13'
    have h13a : (13 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 13).mp ha0
    have ha13n : 13 ∣ a.natAbs := by
      have h := Int.natAbs_dvd_natAbs.mpr h13a
      simpa using h
    have hcop : a.natAbs.Coprime b := by
      have h := x.reduced
      simpa [ha, hb] using h
    have hgcd : Nat.gcd a.natAbs b = 1 := hcop
    have hdvd : 13 ∣ Nat.gcd a.natAbs b := Nat.dvd_gcd ha13n hb13n
    rw [hgcd] at hdvd
    norm_num at hdvd
  · have hb3 : (b : ZMod 13) ^ 3 ≠ 0 := pow_ne_zero 3 hb13
    set r : ZMod 13 := (a : ZMod 13) * (b : ZMod 13)⁻¹ with hr
    have ha_eq : (a : ZMod 13) = r * (b : ZMod 13) := by
      rw [hr]
      field_simp [hb13]
    have hroot : 768 * r ^ 3 + 2176 * r ^ 2 + 400 * r + 625 = 0 := by
      have h := h13
      rw [ha_eq] at h
      have h' : (768 * r ^ 3 + 2176 * r ^ 2 + 400 * r + 625) * (b : ZMod 13) ^ 3 = 0 := by
        rw [show (768 * r ^ 3 + 2176 * r ^ 2 + 400 * r + 625) * (b : ZMod 13) ^ 3 =
            768 * (r * (b : ZMod 13)) ^ 3 + 2176 * (r * (b : ZMod 13)) ^ 2 * (b : ZMod 13) +
              400 * (r * (b : ZMod 13)) * (b : ZMod 13) ^ 2 + 625 * (b : ZMod 13) ^ 3 by ring]
        exact h
      exact (mul_eq_zero.mp h').resolve_right hb3
    exact S1667_residualCubic_noRootMod13 r hroot

/-- The 3-division polynomial with its rational root x = 25/16 split off
(evaluated form). -/
theorem S1667_Ψ₃_eval (x : ℚ) :
    S1667Curve.Ψ₃.eval x =
      (1/256) * (x - 25/16) * (768 * x ^ 3 + 2176 * x ^ 2 + 400 * x + 625) := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [S1667Curve_b₂, S1667Curve_b₄, S1667Curve_b₆, S1667Curve_b₈]
  simp
  ring

theorem S1667_Ψ₃_eval_P : S1667Curve.Ψ₃.eval (25/16) = 0 := by
  rw [S1667_Ψ₃_eval]; norm_num

lemma S1667_nonsingular_P : S1667Curve.toAffine.Nonsingular (25/16) (225/128) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]; norm_num [S1667Curve]
  · norm_num [S1667Curve]

/-- The rational 3-torsion point P = (25/16, 225/128). -/
def S1667P : S1667Curve.toAffine.Point :=
  Affine.Point.some (W' := S1667Curve.toAffine) (25/16) (225/128) S1667_nonsingular_P

lemma S1667P_two : (2 : ℤ) • S1667P = -S1667P := by
  rw [show (2 : ℤ) • S1667P = S1667P + S1667P by rw [two_zsmul]]
  change Affine.Point.some (W' := S1667Curve.toAffine) (25/16) (225/128) S1667_nonsingular_P +
      Affine.Point.some (W' := S1667Curve.toAffine) (25/16) (225/128) S1667_nonsingular_P =
    - Affine.Point.some (W' := S1667Curve.toAffine) (25/16) (225/128) S1667_nonsingular_P
  rw [Affine.Point.neg_some]
  rw [Affine.Point.add_self_of_Y_ne]
  · rw [Affine.Point.some.injEq]
    constructor
    · norm_num [S1667Curve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope]
    · norm_num [S1667Curve, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.slope,
        WeierstrassCurve.Affine.negY]
  · norm_num [S1667Curve, WeierstrassCurve.Affine.negY]

theorem S1667P_three : (3 : ℤ) • S1667P = 0 := by
  have h : (3 : ℤ) • S1667P = S1667P + (2 : ℤ) • S1667P := by
    rw [show (3 : ℤ) = 1 + 2 by norm_num, add_zsmul, one_zsmul]
  rw [h, S1667P_two]
  exact add_neg_cancel S1667P

theorem S1667P_ne_zero : S1667P ≠ 0 :=
  Affine.Point.some_ne_zero S1667_nonsingular_P

/-- The 3-torsion point P has order exactly three. -/
theorem S1667P_order : addOrderOf S1667P = 3 := by
  rw [addOrderOf_eq_iff (by norm_num : 0 < 3)]
  constructor
  · exact S1667P_three
  · intro m hm hpos
    interval_cases m
    · change S1667P ≠ 0
      exact S1667P_ne_zero
    · change (2 : ℤ) • S1667P ≠ 0
      rw [S1667P_two]
      intro h
      exact S1667P_ne_zero (neg_eq_zero.mp h)

/-- The exact 3-division roots: the rational root 25/16 and the residual cubic. -/
theorem S1667_three_division_roots (x : ℚ) :
    S1667Curve.Ψ₃.eval x = 0 ↔ x = 25/16 ∨ S1667ResidualCubic.eval x = 0 := by
  rw [S1667_Ψ₃_eval]
  constructor
  · intro h
    have h' : (x - 25/16) * (768 * x ^ 3 + 2176 * x ^ 2 + 400 * x + 625) = 0 := by
      have h256 : (1/256 : ℚ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp (by simpa using h)).resolve_left h256
    rcases mul_eq_zero.mp h' with h1 | h2
    · left; linarith
    · right; rwa [S1667ResidualCubic_eval]
  · rintro (rfl | h)
    · norm_num
    · rw [S1667ResidualCubic_eval] at h
      rw [h]; ring

/-! ## 4. A rational 6-torsion point -/

lemma S1667_nonsingular_Q : S1667Curve.toAffine.Nonsingular (-5/4) (45/32) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]; norm_num [S1667Curve]
  · norm_num [S1667Curve]

/-- The rational 6-torsion point Q = (-5/4, 45/32) = P + (0,0). -/
def S1667Q : S1667Curve.toAffine.Point :=
  Affine.Point.some (W' := S1667Curve.toAffine) (-5/4) (45/32) S1667_nonsingular_Q

theorem S1667Q_two : (2 : ℤ) • S1667Q = -S1667P := by
  rw [show (2 : ℤ) • S1667Q = S1667Q + S1667Q by rw [two_zsmul]]
  change Affine.Point.some (W' := S1667Curve.toAffine) (-5/4) (45/32) S1667_nonsingular_Q +
      Affine.Point.some (W' := S1667Curve.toAffine) (-5/4) (45/32) S1667_nonsingular_Q =
    - Affine.Point.some (W' := S1667Curve.toAffine) (25/16) (225/128) S1667_nonsingular_P
  rw [Affine.Point.neg_some]
  rw [Affine.Point.add_self_of_Y_ne]
  · rw [Affine.Point.some.injEq]
    constructor
    · norm_num [S1667Curve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope]
    · norm_num [S1667Curve, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.slope,
        WeierstrassCurve.Affine.negY]
  · norm_num [S1667Curve, WeierstrassCurve.Affine.negY]

theorem S1667Q_three : (3 : ℤ) • S1667Q = S1667T0 := by
  have h : (3 : ℤ) • S1667Q = S1667Q + (2 : ℤ) • S1667Q := by
    rw [show (3 : ℤ) = 1 + 2 by norm_num, add_zsmul, one_zsmul]
  rw [h, S1667Q_two]
  change Affine.Point.some (W' := S1667Curve.toAffine) (-5/4) (45/32) S1667_nonsingular_Q +
      (- Affine.Point.some (W' := S1667Curve.toAffine) (25/16) (225/128) S1667_nonsingular_P) =
    Affine.Point.some (W' := S1667Curve.toAffine) 0 0 S1667_nonsingular_zero
  rw [Affine.Point.neg_some]
  rw [Affine.Point.add_of_X_ne]
  · rw [Affine.Point.some.injEq]
    constructor
    · norm_num [S1667Curve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope,
        WeierstrassCurve.Affine.negY]
    · norm_num [S1667Curve, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.slope,
        WeierstrassCurve.Affine.negY]
  · norm_num [S1667Curve, WeierstrassCurve.Affine.negY]

theorem S1667Q_six : (6 : ℤ) • S1667Q = 0 := by
  have h : (6 : ℤ) • S1667Q = (2 : ℤ) • ((3 : ℤ) • S1667Q) := by
    rw [show (6 : ℤ) = 2 * 3 by norm_num, mul_zsmul]
  rw [h, S1667Q_three]
  change (2 : ℤ) • Affine.Point.some (W' := S1667Curve.toAffine) 0 0 S1667_nonsingular_zero = 0
  rw [show (2 : ℤ) • Affine.Point.some (W' := S1667Curve.toAffine) 0 0 S1667_nonsingular_zero =
      Affine.Point.some (W' := S1667Curve.toAffine) 0 0 S1667_nonsingular_zero +
        Affine.Point.some (W' := S1667Curve.toAffine) 0 0 S1667_nonsingular_zero by
    rw [two_zsmul]]
  apply Affine.Point.add_self_of_Y_eq
  norm_num [S1667Curve, WeierstrassCurve.Affine.negY]

theorem S1667Q_ne_zero : S1667Q ≠ 0 :=
  Affine.Point.some_ne_zero S1667_nonsingular_Q

theorem S1667Q_not_two : (2 : ℤ) • S1667Q ≠ 0 := by
  rw [S1667Q_two]
  intro h
  apply S1667P_ne_zero
  exact neg_eq_zero.mp h

theorem S1667Q_not_three : (3 : ℤ) • S1667Q ≠ 0 := by
  rw [S1667Q_three]
  exact S1667T0_ne_zero

/-- The exact order of the rational point Q is six. -/
theorem S1667Q_order : addOrderOf S1667Q = 6 := by
  rw [addOrderOf_eq_iff (by norm_num : 0 < 6)]
  constructor
  · exact S1667Q_six
  · intro m hm hpos
    interval_cases m
    · change S1667Q ≠ 0
      exact S1667Q_ne_zero
    · change (2 : ℤ) • S1667Q ≠ 0
      exact S1667Q_not_two
    · change (3 : ℤ) • S1667Q ≠ 0
      exact S1667Q_not_three
    · change (4 : ℤ) • S1667Q ≠ 0
      rw [show (4 : ℤ) • S1667Q = S1667Q + (3 : ℤ) • S1667Q by
        rw [show (4 : ℤ) = 1 + 3 by norm_num, add_zsmul, one_zsmul]]
      rw [S1667Q_three]
      change Affine.Point.some (W' := S1667Curve.toAffine) (-5/4) (45/32) S1667_nonsingular_Q +
          Affine.Point.some (W' := S1667Curve.toAffine) 0 0 S1667_nonsingular_zero ≠ 0
      rw [Affine.Point.add_of_X_ne (by norm_num)]
      exact Affine.Point.some_ne_zero _
    · change (5 : ℤ) • S1667Q ≠ 0
      rw [show (5 : ℤ) • S1667Q = (2 : ℤ) • S1667Q + (3 : ℤ) • S1667Q by
        rw [show (5 : ℤ) = 2 + 3 by norm_num, add_zsmul]]
      rw [S1667Q_two, S1667Q_three]
      change (- Affine.Point.some (W' := S1667Curve.toAffine) (25/16) (225/128) S1667_nonsingular_P) +
          Affine.Point.some (W' := S1667Curve.toAffine) 0 0 S1667_nonsingular_zero ≠ 0
      rw [Affine.Point.neg_some]
      rw [Affine.Point.add_of_X_ne]
      · exact Affine.Point.some_ne_zero _
      · norm_num [S1667Curve, WeierstrassCurve.Affine.negY]

/-- The 3-division polynomial does not vanish at Q: Q is a 6-torsion point,
not a 3-torsion point. -/
theorem S1667_Ψ₃_eval_Q : S1667Curve.Ψ₃.eval (-5/4) = -91125/4096 := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [S1667Curve_b₂, S1667Curve_b₄, S1667Curve_b₆, S1667Curve_b₈]
  norm_num

theorem S1667_Ψ₂Sq_eval_Q : S1667Curve.Ψ₂Sq.eval (-5/4) = 2025/256 := by
  rw [S1667_Ψ₂Sq_eval]; norm_num

/-! ## 5. Reduction and l-torsion image data -/

/-- The numerator of the discriminant is divisible by 5^6; combined with
Delta = 558140625/1048576 this is v_5(Delta) = 6. -/
theorem S1667_delta_numerator_five_pow_six : (5 ^ 6 : ℕ) ∣ 558140625 := by
  norm_num

theorem S1667_delta_numerator_five_pow_seven_not_dvd : ¬ ((5 ^ 7 : ℕ) ∣ 558140625) := by
  norm_num

/-- The numerator of c_4 is a 5-adic unit: c_4 = 27721/256 and 5 does not
divide 27721. -/
theorem S1667_c4_numerator_not_dvd_five : ¬ ((5 : ℕ) ∣ 27721) := by
  norm_num

/-- The exact type of the l-torsion basis for the concrete curve. -/
abbrev S1667TorsionBasis (l : PrimeGeFive) : Type :=
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (S1667Punctured.LTorsion l)

/-- The literal Serre large-image statement for the concrete curve: the image
of the mod-l Galois representation contains SL_2(F_l).  This is the exact type
of the second D5 field; no inhabitant is asserted here. -/
def S1667SerreLargeImage (l : PrimeGeFive) : Prop :=
  ∃ b : S1667TorsionBasis l,
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (S1667Punctured.galoisLTorsionMatrixRepresentation l b).range

/-- The large-image statement supplies the rank-two torsion basis. -/
theorem S1667TorsionBasis_of_largeImage (l : PrimeGeFive)
    (h : S1667SerreLargeImage l) : Nonempty (S1667TorsionBasis l) := by
  obtain ⟨b, _⟩ := h
  exact ⟨b⟩

/-! ## 6. The exact paper condition (b) and the missing number-field construction -/

/-- The paper condition (b) of IUT I, Definition 3.1, for a curve over F. -/
abbrev S1667PaperConditionB (F : Type) [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F) : Prop :=
  PuncturedEllipticCurve.Torsion23Rational X

/-- The exact remaining construction: a number field F over which the concrete
curve S1667Punctured has all of its 2*3-torsion rational, together with the
two reduction-side conditions of the source clause (an odd residue
characteristic place and split multiplicative reduction there). -/
structure S1667Torsion23Realization where
  F : Type
  [field : Field F]
  [numberField : NumberField F]
  [algebra : Algebra ℚ F]
  place : NumberField.FinitePlace F
  odd_residueCharacteristic : Odd (NumberFieldFinitePlace.residueCharacteristic place)
  torsion23 : PuncturedEllipticCurve.Torsion23Rational (S1667Punctured.baseChange F)
  splitMultiplicative : (S1667Punctured.baseChange F).HasSplitMultiplicativeReductionAt place

/-- The faithful admissible-curve statement: existence of the realization. -/
def S1667Admissible : Prop :=
  Nonempty S1667Torsion23Realization

/-- The first missing construction, stated exactly: a number field with the
base-changed curve satisfying the paper condition (b). -/
def S1667Torsion23FirstMissing : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra ℚ F),
    PuncturedEllipticCurve.Torsion23Rational (S1667Punctured.baseChange F)

/-- A realization gives the first missing construction, i.e. the field part is
exactly what S1667Torsion23Realization adds to the reduction data. -/
theorem S1667Torsion23FirstMissing_of_realization
    (h : S1667Admissible) : S1667Torsion23FirstMissing := by
  obtain ⟨D⟩ := h
  exact ⟨D.F, D.field, D.numberField, D.algebra, D.torsion23⟩

/-- Conversely, if the paper condition (b) is realized over a number field and
the split-multiplicative place is supplied, the admissible data exists.  This is
the exact shape of the remaining obligation. -/
theorem S1667Admissible_of_torsion23
    (F : Type) [Field F] [NumberField F] [Algebra ℚ F]
    (place : NumberField.FinitePlace F)
    (hodd : Odd (NumberFieldFinitePlace.residueCharacteristic place))
    (htor : PuncturedEllipticCurve.Torsion23Rational (S1667Punctured.baseChange F))
    (hsplit : (S1667Punctured.baseChange F).HasSplitMultiplicativeReductionAt place) :
    S1667Admissible :=
  ⟨{ F := F, place := place, odd_residueCharacteristic := hodd,
     torsion23 := htor, splitMultiplicative := hsplit }⟩

/-- The torsion part of the source condition is not the six/l
independence field of the D5 clause: it is the rationality statement itself. -/
theorem S1667PaperConditionB_eq_torsion23
    (F : Type) [Field F] [NumberField F] (X : PuncturedEllipticCurve F) :
    S1667PaperConditionB F X = PuncturedEllipticCurve.Torsion23Rational X := rfl

/-! ## 7. Axiom footprint -/

#print axioms S1667Curve_Δ
#print axioms S1667Curve_isElliptic
#print axioms S1667_Ψ₂Sq_eval
#print axioms S1667T0_two
#print axioms S1667_Ψ₃_eval
#print axioms S1667_Ψ₃_eval_P
#print axioms S1667P_three
#print axioms S1667Q_two
#print axioms S1667Q_three
#print axioms S1667Q_six
#print axioms S1667Q_order
#print axioms S1667_Ψ₃_eval_Q
#print axioms S1667_two_division_roots
#print axioms S1667_three_division_roots
#print axioms S1667ResidualCubic_no_rational_root
#print axioms S1667T0_order
#print axioms S1667P_order
#print axioms S1667T0_ne_T2
#print axioms S1667_delta_numerator_five_pow_six
#print axioms S1667_c4_numerator_not_dvd_five
#print axioms S1667SerreLargeImage
#print axioms S1667TorsionBasis_of_largeImage
#print axioms S1667Torsion23FirstMissing_of_realization
#print axioms S1667Admissible_of_torsion23

end LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

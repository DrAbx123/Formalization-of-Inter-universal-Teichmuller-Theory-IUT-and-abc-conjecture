import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual

/-!
# S1404: integrating the x-coordinate formula with the point-level omega input

This file is the integration layer between

* S1372XCoordinateFormulaActual, which proves the division-polynomial induction
  step xCoordinateFormula_step, and
* the point-level omega identity S1372OmegaFormula, which is the Y-coordinate
  counterpart of the x-coordinate formula and is not available in Mathlib 4.32.2.

## What is proved here (actual, no sorry/axiom)

1. omega holds at n = 0 (vacuously), at n = 1 (immediate), and at n = 2
   (the tangent computation, specialized to psi_2 = 2y + a_1 x + a_3).
2. omega is invariant under n -> -n; hence the all-integer omega input is
   equivalent to the positive-integer input.
3. If the point-level omega identity holds for every positive integer, then the
   x-coordinate formula holds for every positive integer provided all
   psi_1(P), ..., psi_{n+1}(P) are nonzero.  The proof is a strong induction
   using xCoordinateFormula_step, with the two base cases n = 1, 2.

## The exact remaining input

The single global input consumed by the main theorem is

  S1404OmegaInput W : forall n >= 1, S1372OmegaFormula W n.

No attempt is made here to prove S1404OmegaInput; in particular the
IsEllipticNet bridge S1372EllipticNetAtPoint (a Mathlib TODO) is isolated
as S1404EllipticNetInput.

## Exactness caveat on the nonvanishing hypothesis

xCoordinateFormula_step needs psi_k(P) != 0 for all 1 <= k <= n + 1, not only
psi_n(P) != 0.  This is strictly stronger than the hypothesis of
S1372XCoordinateFormula (for example, a point of order 5 has psi_5(P) = 0 but
can still have psi_6(P) != 0).  Consequently the strong statement proved below
does not by itself give the weak target S1372XCoordinateFormula W n from
psi_n(P) != 0 alone.  Removing this nonvanishing hypothesis requires the global
function-field/Jacobian multiplication formula (the Mathlib PR ZSMul theorem),
not the affine induction used by xCoordinateFormula_step.  This file therefore
records the exact last step instead of silently strengthening or weakening the
target.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1404XOmegaIntegrationActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

/-! ## The remaining inputs, as named propositions -/

/-- The point-level omega identity for every positive integer.  This is the
single input consumed by xCoordinateFormula_strong_of_omegaInput. -/
def S1404OmegaInput : Prop :=
  ∀ n : ℤ, 1 ≤ n → S1372OmegaFormula W n

/-- The elliptic-net bridge for the evaluated division-polynomial sequence.
This is the explicit Mathlib 4.32.2 TODO IsEllipticNet (normEDS ...) transported
to a fixed affine point.  It is the exact last algebraic input expected to
yield S1404OmegaInput via the simultaneous x/omega induction. -/
def S1404EllipticNetInput : Prop :=
  ∀ x y : K, S1372EllipticNetAtPoint W x y

/-! ## Base cases and symmetry of the omega identity -/

/-- omega at 0: the hypothesis psi_0 = 0 != 0 is impossible. -/
theorem omegaFormula_zero : S1372OmegaFormula W 0 := by
  intro x y h hne
  exact (hne (by simp)).elim

/-- The omega identity at n = 1: both sides are psi_2 = 2y + a_1 x + a_3. -/
theorem omegaFormula_one : S1372OmegaFormula W 1 := by
  intro x y h hne
  rw [one_zsmul, wCoord_some, show (2 : ℤ) * 1 = 2 by norm_num,
    WeierstrassCurve.evalDivisionPolynomial_two, WeierstrassCurve.evalDivisionPolynomial_one]
  norm_num

/-- The value of psi_2 at the opposite point changes sign. -/
lemma wCoord_neg (P : W.Point) : wCoord W (-P) = - wCoord W P := by
  cases P with
  | zero =>
      change wCoord W (-(0 : W.Point)) = - wCoord W (0 : W.Point)
      simp [wCoord]
  | some x y h =>
      rw [WeierstrassCurve.Affine.Point.neg_some, wCoord_some, wCoord_some,
        WeierstrassCurve.Affine.negY]
      ring

/-- The omega identity is invariant under n -> -n. -/
theorem omegaFormula_neg (n : ℤ) :
    S1372OmegaFormula W n → S1372OmegaFormula W (-n) := by
  intro h x y hns hne
  have hne_n : W.evalDivisionPolynomial x y n ≠ 0 := by
    intro h0
    exact hne (by simpa [W.evalDivisionPolynomial_neg] using congrArg Neg.neg h0)
  have hh := h x y hns hne_n
  have hneg : (-n) • (WeierstrassCurve.Affine.Point.some x y hns) =
      -(n • (WeierstrassCurve.Affine.Point.some x y hns)) := by
    rw [neg_smul]
  rw [hneg, wCoord_neg, hh]
  rw [show 2 * -n = -(2 * n) by ring, W.evalDivisionPolynomial_neg,
    W.evalDivisionPolynomial_neg]
  rw [show (-W.evalDivisionPolynomial x y n) ^ 4 = (W.evalDivisionPolynomial x y n) ^ 4 by
    ring]
  rw [neg_div]

/-- The omega identity at n is equivalent to the one at -n. -/
theorem omegaFormula_neg_iff (n : ℤ) :
    S1372OmegaFormula W n ↔ S1372OmegaFormula W (-n) :=
  ⟨omegaFormula_neg W n, fun h => by simpa using omegaFormula_neg W (-n) h⟩

/-! ## The n = 2 case of the omega identity -/

lemma prePsi_four_eval {x y : K} (h : W.Nonsingular x y) :
    (W.preΨ 4).eval x =
      (W.a₁ * (2 * y + W.a₁ * x + W.a₃) + 2 * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)) *
          (W.preΨ 3).eval x - (2 * y + W.a₁ * x + W.a₃) ^ 4 := by
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (WeierstrassCurve.Affine.equation_iff' (W := W) x y).mp h.1
  rw [show W.preΨ 4 = W.preΨ₄ from by
        rw [show (4:ℤ) = ((4:ℕ):ℤ) by norm_num, WeierstrassCurve.preΨ_ofNat,
          WeierstrassCurve.preΨ'_four],
      show W.preΨ 3 = W.Ψ₃ from by
        rw [show (3:ℤ) = ((3:ℕ):ℤ) by norm_num, WeierstrassCurve.preΨ_ofNat,
          WeierstrassCurve.preΨ'_three]]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  linear_combination (norm := ring)
    (8 * (W.a₁ ^ 2 * x ^ 2 + 2 * W.a₁ * W.a₃ * x + 2 * W.a₁ * x * y + 2 * W.a₂ * x ^ 2 +
      W.a₃ ^ 2 + 2 * W.a₃ * y + 2 * W.a₄ * x + 2 * W.a₆ + 2 * x ^ 3 + 2 * y ^ 2)) * hE

lemma prePsi_four_eval' {x y Bv A : K} (h : W.Nonsingular x y)
    (hB : Bv = 2 * y + W.a₁ * x + W.a₃)
    (hA : A = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) :
    (W.preΨ 4).eval x = (W.a₁ * Bv + 2 * A) * (W.preΨ 3).eval x - Bv ^ 4 := by
  rw [hB, hA]
  exact prePsi_four_eval W h

lemma omega_two_final {Bv A P3 P4 : K}
    (hB : Bv ≠ 0)
    (hpre : P4 = (W.a₁ * Bv + 2 * A) * P3 - Bv ^ 4) :
    -Bv + (W.a₁ * Bv + 2 * A) * P3 / Bv ^ 3 = (P4 * Bv) / Bv ^ 4 := by
  rw [hpre]
  field_simp [hB]
  ring

/-- The omega identity at n = 2: wCoord(2P) = psi_4(P) / psi_2(P)^4. -/
theorem omegaFormula_two {x y : K} (h : W.Nonsingular x y)
    (h2 : W.evalDivisionPolynomial x y 2 ≠ 0) :
    wCoord W ((2 : ℤ) • WeierstrassCurve.Affine.Point.some x y h) =
      W.evalDivisionPolynomial x y 4 /
        (W.evalDivisionPolynomial x y 2) ^ 4 := by
  set Bv : K := 2 * y + W.a₁ * x + W.a₃ with hBdef
  set A : K := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hAdef
  have hB : Bv ≠ 0 := by
    simpa [hBdef, WeierstrassCurve.evalDivisionPolynomial_two] using h2
  have hy : y ≠ W.negY x y := by
    intro hy
    exact h2 ((WeierstrassCurve.evalDivisionPolynomial_two_eq_zero_iff_negY (W := W)).mpr hy)
  have hslope : W.slope x x y y = A / Bv := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    rw [WeierstrassCurve.Affine.negY]
    simp only [hAdef, hBdef]
    congr 1
    ring
  have hX : W.addX x x (W.slope x x y y) = (W.Φ 2).eval x / Bv ^ 2 := by
    have hx2 := xCoordinateFormula_two W x y h h2
    rw [two_zsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy,
      WeierstrassCurve.evalDivisionPolynomial_two] at hx2
    simp only [xCoord_some] at hx2
    exact Option.some.inj hx2
  have hphi2 : (W.Φ 2).eval x = x * Bv ^ 2 - W.evalDivisionPolynomial x y 3 := by
    have hp := phi_eval W h 2
    simpa [hBdef, WeierstrassCurve.evalDivisionPolynomial_two,
      WeierstrassCurve.evalDivisionPolynomial_one] using hp
  have hXsub : W.addX x x (W.slope x x y y) - x =
      - W.evalDivisionPolynomial x y 3 / Bv ^ 2 := by
    rw [hX, hphi2]
    field_simp [hB]
    ring
  have hw : wCoord W (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h) =
      -Bv - (W.a₁ + 2 * (A / Bv)) * (W.addX x x (W.slope x x y y) - x) := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
    simp only [wCoord_some, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, hslope]
    simp only [hBdef, hAdef]
    ring
  have hw2 : wCoord W ((2 : ℤ) • WeierstrassCurve.Affine.Point.some x y h) =
      -Bv + (W.a₁ * Bv + 2 * A) * W.evalDivisionPolynomial x y 3 / Bv ^ 3 := by
    rw [two_zsmul, hw, hXsub]
    field_simp [hB]
    ring
  have hW3 : W.evalDivisionPolynomial x y 3 = (W.preΨ 3).eval x :=
    WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd (W := W) h.1
      (show ¬ Even (3:ℤ) by decide)
  have hW4 : W.evalDivisionPolynomial x y 4 = (W.preΨ 4).eval x * Bv := by
    rw [WeierstrassCurve.evalDivisionPolynomial_eq_evalEval_Ψ (W := W) h.1 4,
      WeierstrassCurve.Ψ_eq_C_preΨ_mul_ψ₂_of_even (W := W) (show Even (4:ℤ) by decide)]
    simp only [Polynomial.evalEval_mul, Polynomial.evalEval_C]
    rw [show Polynomial.evalEval x y (WeierstrassCurve.ψ₂ W) = Bv from by
      rw [hBdef, WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY]]
  rw [hw2, hW3, hW4]
  rw [show W.evalDivisionPolynomial x y 2 = Bv from by
    rw [hBdef, WeierstrassCurve.evalDivisionPolynomial_two]]
  exact omega_two_final W hB (prePsi_four_eval' W h hBdef hAdef)

/-! ## Positive input gives all-integer input -/

/-- If omega holds for every positive integer, it holds for every integer. -/
theorem omegaFormula_all_of_pos
    (h : ∀ n : ℤ, 1 ≤ n → S1372OmegaFormula W n) :
    ∀ n : ℤ, S1372OmegaFormula W n := by
  intro n
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · have h1 : (1 : ℤ) ≤ -n := by omega
    exact (omegaFormula_neg_iff W n).mpr (h (-n) h1)
  · subst hzero
    exact omegaFormula_zero W
  · exact h n (by omega)

/-- S1404OmegaInput is exactly the positive-integer part of the all-integer
omega identity. -/
theorem omegaFormula_all_of_omegaInput (h : S1404OmegaInput W) :
    ∀ n : ℤ, S1372OmegaFormula W n :=
  omegaFormula_all_of_pos W h

/-! ## The strong x-coordinate induction -/

/-- Strong x-coordinate formula from the omega input.

If the point-level omega identity holds at every integer, then for every
N >= 1, every nonsingular point P = (x, y) whose psi_1, ..., psi_{N+1} are all
nonzero satisfies x(N . P) = Phi_N(x) / psi_N(P)^2.

The hypothesis hpsi is exactly what xCoordinateFormula_step consumes; see the
module docstring for why it cannot be dropped inside this affine induction. -/
theorem xCoordinateFormula_strong_of_omega
    (hω : ∀ n : ℤ, S1372OmegaFormula W n) :
    ∀ (N : ℕ), 1 ≤ N → ∀ (x y : K) (h : W.Nonsingular x y),
      (∀ k : ℤ, 1 ≤ k → k ≤ (N : ℤ) + 1 → W.evalDivisionPolynomial x y k ≠ 0) →
      xCoord W ((N : ℤ) • WeierstrassCurve.Affine.Point.some x y h) =
        some ((W.Φ (N : ℤ)).eval x / (W.evalDivisionPolynomial x y (N : ℤ)) ^ 2) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN x y h hψ
    rcases N with _ | _ | _ | M
    · omega
    · simp
    · simpa using xCoordinateFormula_two W x y h (hψ 2 (by norm_num) (by norm_num))
    · let n : ℤ := ((M + 3 : ℕ) : ℤ)
      have hn3 : 3 ≤ n := by dsimp [n]; omega
      have hψn : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0 := by
        intro k hk1 hk2
        exact hψ k hk1 (by dsimp [n] at hk2 ⊢; push_cast at hk2 ⊢; omega)
      have hψM2 : ∀ k : ℤ, 1 ≤ k → k ≤ ((M + 2 : ℕ) : ℤ) + 1 →
          W.evalDivisionPolynomial x y k ≠ 0 := by
        intro k hk1 hk2
        exact hψn k hk1 (by dsimp [n]; push_cast at hk2 ⊢; omega)
      have hψM1 : ∀ k : ℤ, 1 ≤ k → k ≤ ((M + 1 : ℕ) : ℤ) + 1 →
          W.evalDivisionPolynomial x y k ≠ 0 := by
        intro k hk1 hk2
        exact hψn k hk1 (by dsimp [n]; push_cast at hk2 ⊢; omega)
      have hxm1 : xCoord W (((M + 2 : ℕ) : ℤ) •
          WeierstrassCurve.Affine.Point.some x y h) =
          some ((W.Φ ((M + 2 : ℕ) : ℤ)).eval x /
            (W.evalDivisionPolynomial x y ((M + 2 : ℕ) : ℤ)) ^ 2) :=
        ih (M + 2) (by omega) (by omega) x y h hψM2
      have hxm2 : xCoord W (((M + 1 : ℕ) : ℤ) •
          WeierstrassCurve.Affine.Point.some x y h) =
          some ((W.Φ ((M + 1 : ℕ) : ℤ)).eval x /
            (W.evalDivisionPolynomial x y ((M + 1 : ℕ) : ℤ)) ^ 2) :=
        ih (M + 1) (by omega) (by omega) x y h hψM1
      have hxm1' : xCoord W ((n - 1) • WeierstrassCurve.Affine.Point.some x y h) =
          some ((W.Φ (n - 1)).eval x / (W.evalDivisionPolynomial x y (n - 1)) ^ 2) := by
        rw [show n - 1 = ((M + 2 : ℕ) : ℤ) by dsimp [n]; push_cast; ring]
        exact hxm1
      have hxm2' : xCoord W ((n - 2) • WeierstrassCurve.Affine.Point.some x y h) =
          some ((W.Φ (n - 2)).eval x / (W.evalDivisionPolynomial x y (n - 2)) ^ 2) := by
        rw [show n - 2 = ((M + 1 : ℕ) : ℤ) by dsimp [n]; push_cast; ring]
        exact hxm2
      have hωm1 : wCoord W ((n - 1) • WeierstrassCurve.Affine.Point.some x y h) =
          W.evalDivisionPolynomial x y (2 * (n - 1)) /
            (W.evalDivisionPolynomial x y (n - 1)) ^ 4 :=
        hω (n - 1) x y h (hψn (n - 1) (by omega) (by omega))
      exact xCoordinateFormula_step W n hn3 x y h hψn hxm1' hxm2' hωm1

/-- The main integration theorem, stated with the named input S1404OmegaInput. -/
theorem xCoordinateFormula_strong_of_omegaInput (h : S1404OmegaInput W) :
    ∀ (N : ℕ), 1 ≤ N → ∀ (x y : K) (h : W.Nonsingular x y),
      (∀ k : ℤ, 1 ≤ k → k ≤ (N : ℤ) + 1 → W.evalDivisionPolynomial x y k ≠ 0) →
      xCoord W ((N : ℤ) • WeierstrassCurve.Affine.Point.some x y h) =
        some ((W.Φ (N : ℤ)).eval x / (W.evalDivisionPolynomial x y (N : ℤ)) ^ 2) :=
  xCoordinateFormula_strong_of_omega W (omegaFormula_all_of_omegaInput W h)

/-- The same strong statement for an integer exponent `n ≥ 1`, in the form
consumed by the paper-level statements. -/
theorem xCoordinateFormula_strong_of_omegaInput_int
    (h : S1404OmegaInput W) (n : ℤ) (hn : 1 ≤ n)
    (x y : K) (hns : W.Nonsingular x y)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0) :
    xCoord W (n • WeierstrassCurve.Affine.Point.some x y hns) =
      some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2) := by
  have hN : 1 ≤ n.natAbs := by
    have h1 : (1 : ℤ) ≤ (n.natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)]
      omega
    exact_mod_cast h1
  have h' := xCoordinateFormula_strong_of_omegaInput W h n.natAbs hN x y hns (by
    intro k hk1 hk2
    rw [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at hk2
    exact hψ k hk1 hk2)
  rwa [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at h'

/-! ## Axiom footprint -/

#print axioms omegaFormula_zero
#print axioms omegaFormula_one
#print axioms wCoord_neg
#print axioms omegaFormula_neg
#print axioms omegaFormula_neg_iff
#print axioms omegaFormula_two
#print axioms omegaFormula_all_of_pos
#print axioms xCoordinateFormula_strong_of_omega
#print axioms xCoordinateFormula_strong_of_omegaInput
#print axioms xCoordinateFormula_strong_of_omegaInput_int

end LeanFormal.IUT.XiFPaper.S1404XOmegaIntegrationActual

import tmp.sheaf.xif.paper.S1703TorsionCountActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree

/-!
# S1704: the actual geometric 2- and 3-torsion cardinalities

S1702 reduced the remaining torsion inputs to the geometric cardinalities
`Nat.card E[2] = 4` and `Nat.card E[3] = 9`.  This file proves both
statements for the concrete curve
`E : y^2 = x^3 + (61/64) x^2 - (125/64) x` over the algebraic closure of the
S1687 field, without any extra hypothesis, axiom, `sorry`, or fake fill.

## 2-torsion

The 2-division polynomial evaluates as `4 x (x - 1) (x + 125/64)`.  Hence every
affine 2-torsion point has `y = 0` and `x` among the three roots.  The roots
of the 2-division polynomial are separable of degree 3, and the torsion
subtype is equivalent to `Option (rootSet)`, giving `1 + 3 = 4`.

## 3-torsion

For affine points the doubling syzygy and the doubling x-coordinate formula
give the converse of `3 * P = 0 -> Psi3(x) = 0`: a root `x` of `Psi3`
yields `2P = P` or `2P = -P`, hence `3P = 0`.  For such an `x`, the fibre
of `y`-coordinates has exactly two elements (the two square roots of the
Weierstrass right-hand side), and `Psi3` is separable of degree 4.  The
torsion subtype is equivalent to `Option (rootSet, Fin 2)`, giving
`1 + 4 * 2 = 9`.

The file also records the explicit classification facts and the disjointness
of the 2- and 3-division roots. -/

noncomputable section
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S1704TorsionCardActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1702AllTorsionRationalActual
open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial

local instance : DecidableEq S1702Closure := Classical.decEq _

theorem curve_eq : S1702CurveClosure = S1667Curve.baseChange S1702Closure := by
  simp only [S1702CurveClosure, WeierstrassCurve.baseChange, WeierstrassCurve.toAffine]
  rw [WeierstrassCurve.map_map]
  congr 1
theorem a1_zero : S1702CurveClosure.a₁ = 0 := by
  simp [curve_eq, S1667Curve, WeierstrassCurve.baseChange, WeierstrassCurve.map]
theorem a2_eq : S1702CurveClosure.a₂ = (61/64 : S1702Closure) := by
  simp [curve_eq, S1667Curve, WeierstrassCurve.baseChange, WeierstrassCurve.map]
theorem a3_zero : S1702CurveClosure.a₃ = 0 := by
  simp [curve_eq, S1667Curve, WeierstrassCurve.baseChange, WeierstrassCurve.map]
theorem a4_eq : S1702CurveClosure.a₄ = (-125/64 : S1702Closure) := by
  simp [curve_eq, S1667Curve, WeierstrassCurve.baseChange, WeierstrassCurve.map]
theorem a6_zero : S1702CurveClosure.a₆ = 0 := by
  simp [curve_eq, S1667Curve, WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem psi2_eval (x : S1702Closure) :
    S1702CurveClosure.Ψ₂Sq.eval x = 4 * x * (x - 1) * (x + 125/64) := by
  rw [WeierstrassCurve.Ψ₂Sq]
  simp only [curve_eq, S1667Curve, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_ofNat, map_zero, map_ofNat, map_div₀, map_neg]
  ring

theorem psi2_root_cases {x : S1702Closure}
    (hx : S1702CurveClosure.Ψ₂Sq.eval x = 0) :
    x = 0 ∨ x = 1 ∨ x = -125/64 := by
  rw [psi2_eval] at hx
  have h4 : (4 : S1702Closure) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hx with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl ((mul_eq_zero.mp h).resolve_left h4)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (by linear_combination h))

theorem psi3_eval (x : S1702Closure) :
    S1702CurveClosure.Ψ₃.eval x =
      (1/256) * (x - 25/16) * (768 * x^3 + 2176 * x^2 + 400 * x + 625) := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [curve_eq, S1667Curve, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_ofNat, map_zero, map_ofNat, map_div₀, map_neg]
  ring

theorem psi3_root_cases {x : S1702Closure}
    (hx : S1702CurveClosure.Ψ₃.eval x = 0) :
    x = 25/16 ∨ 768 * x^3 + 2176 * x^2 + 400 * x + 625 = 0 := by
  rw [psi3_eval] at hx
  have hc : (1/256 : S1702Closure) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hx with h | h
  · exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc))
  · exact Or.inr h

theorem psi2_psi3_disjoint {x : S1702Closure}
    (h2 : S1702CurveClosure.Ψ₂Sq.eval x = 0)
    (h3 : S1702CurveClosure.Ψ₃.eval x = 0) : False := by
  rcases psi2_root_cases h2 with rfl | rfl | rfl
  · rw [psi3_eval] at h3; norm_num at h3
  · rw [psi3_eval] at h3; norm_num at h3
  · rw [psi3_eval] at h3; norm_num at h3


theorem psi2_eval_of_two_torsion {x y : S1702Closure}
    (hns : S1702CurveClosure.Nonsingular x y)
    (h2 : (2 : ℤ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) = 0) :
    S1702CurveClosure.Ψ₂Sq.eval x = 0 := by
  have h2' : (2 : ℕ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) = 0 := by
    rwa [show (2 : ℤ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) =
      (2 : ℕ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) from
      natCast_zsmul _ 2] at h2
  have hpsi := (WeierstrassCurve.two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero
    S1702CurveClosure hns).mp h2'
  rw [WeierstrassCurve.evalDivisionPolynomial_two] at hpsi
  have hsq := WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq S1702CurveClosure hns.1 2
  rw [WeierstrassCurve.Ψ_two, WeierstrassCurve.ΨSq_two,
    WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY, hpsi] at hsq
  simpa using hsq.symm

theorem y_eq_zero_of_two_torsion {x y : S1702Closure}
    (hns : S1702CurveClosure.Nonsingular x y)
    (h2 : (2 : ℤ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) = 0) :
    y = 0 := by
  have h2' : (2 : ℕ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) = 0 := by
    rwa [show (2 : ℤ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) =
      (2 : ℕ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) from
      natCast_zsmul _ 2] at h2
  have hpsi := (WeierstrassCurve.two_nsmul_some_eq_zero_iff_evalDivisionPolynomial_two_eq_zero
    S1702CurveClosure hns).mp h2'
  rw [WeierstrassCurve.evalDivisionPolynomial_two, a1_zero, a3_zero] at hpsi
  simp only [zero_mul, add_zero] at hpsi
  exact (mul_eq_zero.mp hpsi).resolve_left (by norm_num)

theorem nonsingular_zero_of_psi2_root {x : S1702Closure}
    (hx : S1702CurveClosure.Ψ₂Sq.eval x = 0) :
    S1702CurveClosure.Nonsingular x 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    rw [a1_zero, a2_eq, a3_zero, a4_eq, a6_zero]
    have hx' : 4 * x * (x - 1) * (x + 125/64) = 0 := by rw [← psi2_eval]; exact hx
    have hx'' : (4 : S1702Closure) * (x * (x - 1) * (x + 125/64)) = 0 := by
      simpa only [mul_assoc] using hx'
    have hg : x * (x - 1) * (x + 125/64) = 0 :=
      (mul_eq_zero.mp hx'').resolve_left (by norm_num)
    have hpoly : x * (x - 1) * (x + 125/64) =
        x ^ 3 + (61/64 : S1702Closure) * x ^ 2 + (-125/64 : S1702Closure) * x := by ring
    rw [hpoly] at hg
    rw [show (0 : S1702Closure) ^ 2 = 0 by norm_num]
    simp only [zero_mul, mul_zero, add_zero]
    exact hg.symm
  · rw [a1_zero, a2_eq, a3_zero, a4_eq]
    rcases psi2_root_cases hx with rfl | rfl | rfl
    · left; norm_num
    · left; norm_num
    · left; norm_num

abbrev TwoRoots : Set S1702Closure := S1667Curve.Ψ₂Sq.rootSet S1702Closure

theorem mem_twoRoots {x : S1702Closure} :
    x ∈ TwoRoots ↔ S1702CurveClosure.Ψ₂Sq.eval x = 0 := by
  rw [TwoRoots,
    Polynomial.mem_rootSet_of_ne (S1667Curve.Ψ₂Sq_ne_zero (by norm_num : (4:ℚ) ≠ 0))]
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    show S1702CurveClosure.Ψ₂Sq = S1667Curve.Ψ₂Sq.map (algebraMap ℚ S1702Closure) by
      rw [curve_eq]; exact WeierstrassCurve.map_Ψ₂Sq _ _]

def twoTorsionPoint (x : S1702Closure) (hx : S1702CurveClosure.Ψ₂Sq.eval x = 0) : S1702ClosurePoint :=
  Affine.Point.some (W' := S1702CurveClosure) x 0 (nonsingular_zero_of_psi2_root hx)

theorem twoTorsionPoint_two (x : S1702Closure) (hx : S1702CurveClosure.Ψ₂Sq.eval x = 0) :
    (2 : ℤ) • twoTorsionPoint x hx = 0 := by
  rw [show (2 : ℤ) • twoTorsionPoint x hx = twoTorsionPoint x hx + twoTorsionPoint x hx by
    rw [two_zsmul]]
  apply Affine.Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY]

def twoTorsionToFun : {P : S1702ClosurePoint // (2 : ℤ) • P = 0} → Option (TwoRoots : Type)
  | ⟨0, _⟩ => none
  | ⟨Affine.Point.some x _ hns, hP⟩ =>
      some ⟨x, mem_twoRoots.mpr (psi2_eval_of_two_torsion hns hP)⟩

def twoTorsionInvFun : Option (TwoRoots : Type) → {P : S1702ClosurePoint // (2 : ℤ) • P = 0}
  | none => ⟨0, zsmul_zero 2⟩
  | some r => ⟨twoTorsionPoint r.1 (mem_twoRoots.mp r.2),
      twoTorsionPoint_two r.1 (mem_twoRoots.mp r.2)⟩

theorem twoTorsion_left_inv (P : {P : S1702ClosurePoint // (2 : ℤ) • P = 0}) :
    twoTorsionInvFun (twoTorsionToFun P) = P := by
  rcases P with ⟨P, hP⟩
  cases P with
  | zero => rfl
  | some x y hns =>
      have hy : y = 0 := y_eq_zero_of_two_torsion hns hP
      subst hy
      apply Subtype.ext
      exact (Affine.Point.some.injEq x 0
        (nonsingular_zero_of_psi2_root (psi2_eval_of_two_torsion hns hP)) x 0 hns).mpr
        ⟨rfl, rfl⟩

theorem twoTorsion_right_inv (o : Option (TwoRoots : Type)) :
    twoTorsionToFun (twoTorsionInvFun o) = o := by
  cases o with
  | none => rfl
  | some r =>
      apply congrArg some
      apply Subtype.ext
      rfl

def twoTorsionEquiv :
    {P : S1702ClosurePoint // (2 : ℤ) • P = 0} ≃ Option (TwoRoots : Type) where
  toFun := twoTorsionToFun
  invFun := twoTorsionInvFun
  left_inv := twoTorsion_left_inv
  right_inv := twoTorsion_right_inv

theorem psi2_factor : S1667Curve.Ψ₂Sq =
    C 4 * ((X - C (0:ℚ)) * (X - C 1) * (X - C (-125/64))) := by
  apply Polynomial.funext
  intro x
  rw [S1667_Ψ₂Sq_eval]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  ring

theorem psi2_prod_separable :
    (((X - C (0:ℚ)) * (X - C 1) * (X - C (-125/64)))).Separable := by
  have h01 : IsCoprime (X - C (0:ℚ)) (X - C 1) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by norm_num : IsUnit ((0:ℚ) - 1))
  have h02 : IsCoprime (X - C (0:ℚ)) (X - C (-125/64)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by norm_num : IsUnit ((0:ℚ) - (-125/64)))
  have h12 : IsCoprime (X - C (1:ℚ)) (X - C (-125/64)) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by norm_num : IsUnit ((1:ℚ) - (-125/64)))
  have h01' : IsCoprime ((X - C (0:ℚ)) * (X - C 1)) (X - C (-125/64)) :=
    IsCoprime.mul_left h02 h12
  exact Separable.mul
    (Separable.mul Polynomial.separable_X_sub_C Polynomial.separable_X_sub_C h01)
    Polynomial.separable_X_sub_C h01'

theorem psi2_separable : S1667Curve.Ψ₂Sq.Separable := by
  rw [psi2_factor]
  rw [mul_comm (C (4:ℚ)) (((X - C (0:ℚ)) * (X - C 1)) * (X - C (-125/64)))]
  exact Separable.mul_unit psi2_prod_separable (isUnit_C.mpr (by norm_num : IsUnit (4:ℚ)))

theorem two_root_card : Fintype.card (S1667Curve.Ψ₂Sq.rootSet S1702Closure) = 3 := by
  rw [Polynomial.card_rootSet_eq_natDegree (K := S1702Closure) psi2_separable
    (IsAlgClosed.splits _)]
  rw [WeierstrassCurve.natDegree_Ψ₂Sq (W := S1667Curve) (by norm_num : (4:ℚ) ≠ 0)]

theorem twoTorsionCard : Nat.card {P : S1702ClosurePoint // (2 : ℤ) • P = 0} = 4 := by
  rw [Nat.card_congr twoTorsionEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_option]
  have h : Fintype.card (TwoRoots : Type) = 3 := by
    simpa [TwoRoots] using two_root_card
  rw [h]


theorem three_nsmul_some_eq_zero_of_psi3_root {x y : S1702Closure}
    (hns : S1702CurveClosure.Nonsingular x y)
    (hpsi : S1702CurveClosure.Ψ₃.eval x = 0) :
    (3 : ℤ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) = 0 := by
  classical
  set W := S1702CurveClosure with hW
  set A : S1702Closure := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y with hA
  set B : S1702Closure := 2 * y + W.a₁ * x + W.a₃ with hB
  have hB_ne : B ≠ 0 := by
    intro hB0
    have hpsi2 : W.Ψ₂Sq.eval x = 0 := by
      have hpsi_two : W.evalDivisionPolynomial x y 2 = 0 := by
        rw [WeierstrassCurve.evalDivisionPolynomial_two]
        exact hB0
      have hsq := WeierstrassCurve.evalEval_Ψ_sq_eq_eval_ΨSq W hns.1 2
      rw [← WeierstrassCurve.evalDivisionPolynomial_eq_evalEval_Ψ W hns.1 2,
        hpsi_two, WeierstrassCurve.ΨSq_two] at hsq
      simpa using hsq.symm
    exact psi2_psi3_disjoint hpsi2 hpsi
  have hy_ne : y ≠ W.toAffine.negY x y := by
    intro hy
    apply hB_ne
    rw [WeierstrassCurve.Affine.negY] at hy
    linear_combination hy
  have hslope : W.toAffine.slope x x y y = A / B := by
    have hy' : ¬ y = -y - W.a₁ * x - W.a₃ := by
      simpa only [WeierstrassCurve.Affine.negY] using hy_ne
    rw [WeierstrassCurve.Affine.slope_of_Y_ne' hy', hA, hB]
    ring
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (WeierstrassCurve.Affine.equation_iff' (W := W.toAffine) x y).mp hns.1
  have hPhi : (W.Φ 2).eval x = A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 := by
    rw [hA, hB, WeierstrassCurve.Φ_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * hE
  have hPsi2Sq : (W.Ψ₂Sq).eval x = B ^ 2 := by
    rw [hB, WeierstrassCurve.Ψ₂Sq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination (-4) * hE
  have hsplit : W.Ψ₃.eval x = x * (W.Ψ₂Sq).eval x - (W.Φ 2).eval x := by
    rw [WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Φ_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat]
    ring
  have hPhi_eq : (W.Φ 2).eval x = x * B ^ 2 := by
    have hzero : x * (W.Ψ₂Sq).eval x - (W.Φ 2).eval x = 0 := by
      rw [← hsplit, hpsi]
    have := sub_eq_zero.mp hzero
    rw [hPsi2Sq] at this
    exact this.symm
  have haddX : W.toAffine.addX x x (A / B) * B ^ 2 =
      A ^ 2 + W.a₁ * A * B - (W.a₂ + 2 * x) * B ^ 2 := by
    simp only [WeierstrassCurve.Affine.addX]
    field_simp [hB_ne]
    ring
  have hX : W.toAffine.addX x x (A / B) = x := by
    have hB2 : B ^ 2 ≠ 0 := pow_ne_zero 2 hB_ne
    apply mul_right_cancel₀ hB2
    rw [haddX, ← hPhi]
    exact hPhi_eq
  have hPP : (Affine.Point.some (W' := W) x y hns) + (Affine.Point.some (W' := W) x y hns) =
      Affine.Point.some (W' := W) (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.addY x x y (W.toAffine.slope x x y y))
        (WeierstrassCurve.Affine.nonsingular_add hns hns (fun hxy => hy_ne hxy.2)) :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_ne
  have hPne : (Affine.Point.some (W' := W) x y hns) ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hns
  have hdisj : (Affine.Point.some (W' := W) x y hns) + (Affine.Point.some (W' := W) x y hns) =
      Affine.Point.some (W' := W) x y hns ∨
      (Affine.Point.some (W' := W) x y hns) + (Affine.Point.some (W' := W) x y hns) =
        -Affine.Point.some (W' := W) x y hns := by
    have hxeq : W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
      rw [hslope, hX]
    have h := (WeierstrassCurve.Affine.Point.X_eq_iff
      (x₁ := W.toAffine.addX x x (W.toAffine.slope x x y y))
      (y₁ := W.toAffine.addY x x y (W.toAffine.slope x x y y))
      (x₂ := x) (y₂ := y)
      (h₁ := WeierstrassCurve.Affine.nonsingular_add hns hns (fun hxy => hy_ne hxy.2))
      (h₂ := hns)).mp hxeq
    simpa only [← hPP] using h
  rcases hdisj with hcase | hcase
  · exfalso
    have hP0 : (Affine.Point.some (W' := W) x y hns) = 0 := by
      have hsame : (Affine.Point.some (W' := W) x y hns) +
          (Affine.Point.some (W' := W) x y hns) =
          (Affine.Point.some (W' := W) x y hns) + 0 := by
        rw [add_zero, hcase]
      exact add_left_cancel hsame
    exact hPne hP0
  · let S : S1702ClosurePoint := Affine.Point.some (W' := W) x y hns
    have hS : S = Affine.Point.some (W' := W) x y hns := rfl
    calc
      (3 : ℤ) • S = (3 : ℕ) • S := natCast_zsmul S 3
      _ = S + (S + S) := three_nsmul S
      _ = (S + S) + S := by abel
      _ = (-S) + S := by rw [hS, hcase]
      _ = 0 := neg_add_cancel S


theorem psi3_map : S1702CurveClosure.Ψ₃ = S1667Curve.Ψ₃.map (algebraMap ℚ S1702Closure) := by
  rw [curve_eq]
  exact WeierstrassCurve.map_Ψ₃ S1667Curve (algebraMap ℚ S1702Closure)

abbrev ThreeRoots : Set S1702Closure := S1667Curve.Ψ₃.rootSet S1702Closure

theorem mem_threeRoots {x : S1702Closure} :
    x ∈ ThreeRoots ↔ S1702CurveClosure.Ψ₃.eval x = 0 := by
  rw [ThreeRoots,
    Polynomial.mem_rootSet_of_ne (S1667Curve.Ψ₃_ne_zero (by norm_num : (3:ℚ) ≠ 0))]
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, psi3_map]

abbrev ThreeFiber (x : S1702Closure) : Type :=
  {y : S1702Closure // S1702CurveClosure.Nonsingular x y}

def S1704G (x : S1702Closure) : S1702Closure :=
  x ^ 3 + (61/64 : S1702Closure) * x ^ 2 + (-125/64 : S1702Closure) * x

theorem psi2_eval_g (x : S1702Closure) :
    S1702CurveClosure.Ψ₂Sq.eval x = 4 * S1704G x := by
  rw [psi2_eval]
  unfold S1704G
  ring

theorem g_ne_zero_of_psi3_root {x : S1702Closure}
    (h3 : S1702CurveClosure.Ψ₃.eval x = 0) : S1704G x ≠ 0 := by
  intro hg
  have h2 : S1702CurveClosure.Ψ₂Sq.eval x = 0 := by
    rw [psi2_eval_g, hg, mul_zero]
  exact psi2_psi3_disjoint h2 h3

theorem equation_of_y_sq {x y : S1702Closure}
    (hy : y ^ 2 = S1704G x) :
    S1702CurveClosure.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  rw [a1_zero, a2_eq, a3_zero, a4_eq, a6_zero]
  unfold S1704G at hy
  linear_combination hy

theorem y_sq_of_nonsingular {x y : S1702Closure}
    (hns : S1702CurveClosure.Nonsingular x y) :
    y ^ 2 = S1704G x := by
  have hEq := hns.1
  rw [WeierstrassCurve.Affine.equation_iff, a1_zero, a2_eq, a3_zero, a4_eq, a6_zero] at hEq
  unfold S1704G
  linear_combination hEq

theorem nonsingular_of_y_sq {x y : S1702Closure}
    (hy : y ^ 2 = S1704G x) (hy0 : y ≠ 0) :
    S1702CurveClosure.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  constructor
  · exact equation_of_y_sq hy
  · right
    rw [a1_zero, a3_zero]
    intro h
    have h2 : (2 : S1702Closure) * y = 0 := by linear_combination h
    exact hy0 ((mul_eq_zero.mp h2).resolve_left (by norm_num))

theorem y_eq_or_neg_of_nonsingular {x y y0 : S1702Closure}
    (hns : S1702CurveClosure.Nonsingular x y) (hy0 : y0 ^ 2 = S1704G x) :
    y = y0 ∨ y = -y0 := by
  have hy : y ^ 2 = S1704G x := y_sq_of_nonsingular hns
  have hsq : y ^ 2 = y0 ^ 2 := by rw [hy, hy0]
  have hfac : (y - y0) * (y + y0) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · left; linear_combination h
  · right; linear_combination h

noncomputable def fiberEquiv (x : S1702Closure)
    (hpsi : S1702CurveClosure.Ψ₃.eval x = 0) : Fin 2 ≃ ThreeFiber x := by
  classical
  have hg : S1704G x ≠ 0 := g_ne_zero_of_psi3_root hpsi
  let y0 : S1702Closure := Classical.choose
    (IsAlgClosed.exists_pow_nat_eq (S1704G x) (by decide : 0 < 2))
  have hy0_sq : y0 ^ 2 = S1704G x := Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (S1704G x) (by decide : 0 < 2))
  have hy0_ne : y0 ≠ 0 := by
    intro h0
    apply hg
    rw [← hy0_sq, h0]
    ring
  have hy0_ne_neg : y0 ≠ -y0 := by
    intro h
    have h2 : (2 : S1702Closure) * y0 = 0 := by linear_combination h
    exact hy0_ne ((mul_eq_zero.mp h2).resolve_left (by norm_num))
  have hneg_ne : -y0 ≠ 0 := neg_ne_zero.mpr hy0_ne
  exact {
    toFun := fun i => if i = 0 then
        ⟨y0, nonsingular_of_y_sq hy0_sq hy0_ne⟩
      else
        ⟨-y0, nonsingular_of_y_sq (by rw [neg_sq, hy0_sq]) hneg_ne⟩
    invFun := fun y => if y.1 = y0 then 0 else 1
    left_inv := by
      intro i
      fin_cases i
      · simp
      · simp [hy0_ne_neg.symm]
    right_inv := by
      intro y
      by_cases hy : y.1 = y0
      · simp only [hy, if_pos]
        apply Subtype.ext
        exact hy.symm
      · have hyneg : y.1 = -y0 := by
          rcases y_eq_or_neg_of_nonsingular y.2 hy0_sq with h | h
          · exact (hy h).elim
          · exact h
        simp [hy]
        apply Subtype.ext
        exact hyneg.symm
  }

theorem fiber_card {x : S1702Closure} (hpsi : S1702CurveClosure.Ψ₃.eval x = 0) :
    Nat.card (ThreeFiber x) = 2 := by
  rw [← Nat.card_congr (fiberEquiv x hpsi)]
  simp

theorem psi3_eval_of_three_torsion {x y : S1702Closure}
    (hns : S1702CurveClosure.Nonsingular x y)
    (h3 : (3 : ℤ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) = 0) :
    S1702CurveClosure.Ψ₃.eval x = 0 := by
  have h3' : (3 : ℕ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) = 0 := by
    rwa [show (3 : ℤ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) =
      (3 : ℕ) • (Affine.Point.some (W' := S1702CurveClosure) x y hns) from
      natCast_zsmul _ 3] at h3
  have h := WeierstrassCurve.evalDivisionPolynomialAtPoint_three_eq_zero_of_three_nsmul_eq_zero
    S1702CurveClosure (Affine.Point.some (W' := S1702CurveClosure) x y hns) h3'
  rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
    WeierstrassCurve.evalDivisionPolynomial_eq_eval_preΨ_of_odd S1702CurveClosure hns.1
      (by decide : ¬ Even (3 : ℤ)),
    WeierstrassCurve.preΨ_three] at h
  exact h

abbrev ThreePair : Type :=
  {p : S1702Closure × S1702Closure //
    p.1 ∈ ThreeRoots ∧ S1702CurveClosure.Nonsingular p.1 p.2}

def threeTorsionToFun : {P : S1702ClosurePoint // (3 : ℤ) • P = 0} → Option ThreePair
  | ⟨0, _⟩ => none
  | ⟨Affine.Point.some x y hns, hP⟩ =>
      some ⟨(x, y), ⟨mem_threeRoots.mpr (psi3_eval_of_three_torsion hns hP), hns⟩⟩

def threeTorsionInvFun : Option ThreePair → {P : S1702ClosurePoint // (3 : ℤ) • P = 0}
  | none => ⟨0, zsmul_zero 3⟩
  | some p => ⟨Affine.Point.some (W' := S1702CurveClosure) p.1.1 p.1.2 p.2.2,
      three_nsmul_some_eq_zero_of_psi3_root p.2.2 (mem_threeRoots.mp p.2.1)⟩

theorem threeTorsion_left_inv (P : {P : S1702ClosurePoint // (3 : ℤ) • P = 0}) :
    threeTorsionInvFun (threeTorsionToFun P) = P := by
  rcases P with ⟨P, hP⟩
  cases P with
  | zero => rfl
  | some x y hns =>
      apply Subtype.ext
      rfl

theorem threeTorsion_right_inv (o : Option ThreePair) :
    threeTorsionToFun (threeTorsionInvFun o) = o := by
  cases o with
  | none => rfl
  | some p =>
      apply congrArg some
      apply Subtype.ext
      rfl

def threeTorsionEquiv :
    {P : S1702ClosurePoint // (3 : ℤ) • P = 0} ≃ Option ThreePair where
  toFun := threeTorsionToFun
  invFun := threeTorsionInvFun
  left_inv := threeTorsion_left_inv
  right_inv := threeTorsion_right_inv

def sigmaEquivPair : (Σ x : ThreeRoots, ThreeFiber x.1) ≃ ThreePair where
  toFun s := ⟨(s.1.1, s.2.1), ⟨s.1.2, s.2.2⟩⟩
  invFun p := ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
  left_inv := by intro s; rfl
  right_inv := by intro p; rfl

noncomputable instance threeFiberFintype (x : ThreeRoots) : Fintype (ThreeFiber x.1) :=
  Fintype.ofEquiv (Fin 2) (fiberEquiv x.1 (mem_threeRoots.mp x.2))

noncomputable instance threePairFintype : Fintype ThreePair :=
  Fintype.ofEquiv (Σ x : ThreeRoots, ThreeFiber x.1) sigmaEquivPair

theorem threeFiberFintype_card (x : ThreeRoots) : Fintype.card (ThreeFiber x.1) = 2 := by
  rw [← Nat.card_eq_fintype_card]
  exact fiber_card (mem_threeRoots.mp x.2)

theorem psi3_factor : S1667Curve.Ψ₃ =
    C (1/256) * (X - C (25/16)) * S1667ResidualCubic := by
  apply Polynomial.funext
  intro x
  rw [S1667_Ψ₃_eval]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat,
    S1667ResidualCubic]

theorem residual_natDegree_le : S1667ResidualCubic.natDegree ≤ 3 := by
  rw [S1667ResidualCubic]
  compute_degree

theorem residual_coeff_three : S1667ResidualCubic.coeff 3 = 768 := by
  simp [S1667ResidualCubic, Polynomial.coeff_X, Polynomial.coeff_X_pow]

theorem residual_natDegree : S1667ResidualCubic.natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero residual_natDegree_le
  rw [residual_coeff_three]
  norm_num

theorem residual_derivative_ne_zero : derivative S1667ResidualCubic ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 2) h
  rw [Polynomial.coeff_derivative, residual_coeff_three] at hc
  norm_num at hc

theorem residual_irreducible : Irreducible S1667ResidualCubic := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc]
    exact ⟨by rw [residual_natDegree]; norm_num, by rw [residual_natDegree]⟩
  · intro x hx
    exact S1667ResidualCubic_no_rational_root ⟨x, hx⟩

theorem residual_separable : S1667ResidualCubic.Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero residual_irreducible]
  exact residual_derivative_ne_zero

theorem linear_not_dvd_residual : ¬ (X - C (25/16) : ℚ[X]) ∣ S1667ResidualCubic := by
  rw [Polynomial.dvd_iff_isRoot]
  intro h
  have hval : S1667ResidualCubic.eval (25/16) = 0 := h
  rw [S1667ResidualCubic] at hval
  norm_num at hval

theorem linear_coprime_residual : IsCoprime (X - C (25/16) : ℚ[X]) S1667ResidualCubic := by
  have hprime : Prime (X - C (25/16) : ℚ[X]) := Polynomial.prime_X_sub_C _
  exact (hprime.coprime_iff_not_dvd).mpr linear_not_dvd_residual

theorem psi3_separable : S1667Curve.Ψ₃.Separable := by
  rw [psi3_factor]
  have hlin : (X - C (25/16) : ℚ[X]).Separable := Polynomial.separable_X_sub_C
  have hres : S1667ResidualCubic.Separable := residual_separable
  have hprod : ((X - C (25/16) : ℚ[X]) * S1667ResidualCubic).Separable :=
    Separable.mul hlin hres linear_coprime_residual
  rw [mul_assoc, mul_comm (C (1/256) : ℚ[X])]
  exact Separable.mul_unit hprod (isUnit_C.mpr (by norm_num : IsUnit (1/256 : ℚ)))

theorem three_root_card : Fintype.card (S1667Curve.Ψ₃.rootSet S1702Closure) = 4 := by
  rw [Polynomial.card_rootSet_eq_natDegree (K := S1702Closure) psi3_separable
    (IsAlgClosed.splits _)]
  rw [WeierstrassCurve.natDegree_Ψ₃ (W := S1667Curve) (by norm_num : (3:ℚ) ≠ 0)]

theorem threePairCard : Nat.card ThreePair = 8 := by
  rw [← Nat.card_congr sigmaEquivPair]
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [threeFiberFintype_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show Fintype.card ThreeRoots = 4 by simpa [ThreeRoots] using three_root_card]
  norm_num

theorem threeTorsionCard : Nat.card {P : S1702ClosurePoint // (3 : ℤ) • P = 0} = 9 := by
  rw [Nat.card_congr threeTorsionEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_option]
  rw [show Fintype.card ThreePair = 8 by
    rw [← Nat.card_eq_fintype_card]
    exact threePairCard]


/-- The exact S1702 geometric 2-torsion cardinality, proved. -/
theorem S1704GeometricTwoTorsionCard : S1702GeometricTwoTorsionCard :=
  twoTorsionCard

/-- The exact S1702 geometric 3-torsion cardinality, proved. -/
theorem S1704GeometricThreeTorsionCard : S1702GeometricThreeTorsionCard :=
  threeTorsionCard

#check S1704GeometricTwoTorsionCard
#check S1704GeometricThreeTorsionCard
#print axioms S1704GeometricTwoTorsionCard
#print axioms S1704GeometricThreeTorsionCard

end LeanFormal.IUT.XiFPaper.S1704TorsionCardActual
end

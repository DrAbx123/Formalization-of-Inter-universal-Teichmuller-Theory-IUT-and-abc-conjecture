import tmp.sheaf.xif.paper.S1372XCoordinateFormulaActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual

open Polynomial
open LeanFormal.IUT
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

lemma xCoord_neg (P : W.Point) : xCoord W (-P) = xCoord W P := by
  cases P with
  | zero => rfl
  | some x y h => rw [WeierstrassCurve.Affine.Point.neg_some, xCoord_some, xCoord_some]

/-- One step of the division-polynomial induction for the x-coordinate. -/
theorem xCoordinateFormula_step
    (n : ℤ) (hn3 : 3 ≤ n) (x y : K) (h : W.Nonsingular x y)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0)
    (hxm1 : xCoord W ((n - 1) • WeierstrassCurve.Affine.Point.some x y h) =
      some ((W.Φ (n - 1)).eval x / (W.evalDivisionPolynomial x y (n - 1)) ^ 2))
    (hxm2 : xCoord W ((n - 2) • WeierstrassCurve.Affine.Point.some x y h) =
      some ((W.Φ (n - 2)).eval x / (W.evalDivisionPolynomial x y (n - 2)) ^ 2))
    (hω : wCoord W ((n - 1) • WeierstrassCurve.Affine.Point.some x y h) =
      W.evalDivisionPolynomial x y (2 * (n - 1)) /
        (W.evalDivisionPolynomial x y (n - 1)) ^ 4) :
    xCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
      some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2) := by
  let P0 : W.Point := WeierstrassCurve.Affine.Point.some x y h
  have hn1 : (1 : ℤ) ≤ n := by linarith
  have hψ_n : W.evalDivisionPolynomial x y n ≠ 0 := hψ n hn1 (by linarith)
  have hψ_nm1 : W.evalDivisionPolynomial x y (n - 1) ≠ 0 := hψ (n - 1) (by linarith) (by linarith)
  have hψ_nm2 : W.evalDivisionPolynomial x y (n - 2) ≠ 0 := hψ (n - 2) (by linarith) (by linarith)
  have hψ_np1 : W.evalDivisionPolynomial x y (n + 1) ≠ 0 := hψ (n + 1) (by linarith) (by linarith)
  rcases hQ : ((n - 1) • P0) with _ | ⟨u, v, hQns⟩
  · rw [hQ] at hxm1
    simp [xCoord] at hxm1
  · rw [hQ] at hxm1 hω
    have hu : u = (W.Φ (n - 1)).eval x / (W.evalDivisionPolynomial x y (n - 1)) ^ 2 := by
      simpa [xCoord] using hxm1
    have hwQ : 2 * v + W.a₁ * u + W.a₃ =
        W.evalDivisionPolynomial x y (2 * (n - 1)) /
          (W.evalDivisionPolynomial x y (n - 1)) ^ 4 := by
      simpa [wCoord] using hω
    have hphi_nm1 := phi_eval W h (n - 1)
    have hphi_nm1' : (W.Φ (n - 1)).eval x =
        x * (W.evalDivisionPolynomial x y (n - 1)) ^ 2 -
          W.evalDivisionPolynomial x y n * W.evalDivisionPolynomial x y (n - 2) := by
      simpa [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring] using hphi_nm1
    have hux : u ≠ x := by
      intro hux
      have h0 : W.evalDivisionPolynomial x y n * W.evalDivisionPolynomial x y (n - 2) = 0 := by
        have h1 : u - x = 0 := sub_eq_zero.mpr hux
        rw [hu, hphi_nm1'] at h1
        field_simp [hψ_nm1] at h1
        linear_combination -h1
      exact mul_ne_zero hψ_n hψ_nm2 h0
    rcases hR : ((n - 2) • P0) with _ | ⟨s, t, hRns⟩
    · rw [hR] at hxm2
      simp [xCoord] at hxm2
    · rw [hR] at hxm2
      have hs : s = (W.Φ (n - 2)).eval x / (W.evalDivisionPolynomial x y (n - 2)) ^ 2 := by
        simpa [xCoord] using hxm2
      have hrec := xCoord_recurrence W h hQns hux
      have hplus : P0 + WeierstrassCurve.Affine.Point.some u v hQns = n • P0 := by
        rw [← hQ]
        calc P0 + (n - 1) • P0 = (1 : ℤ) • P0 + (n - 1) • P0 := by rw [one_zsmul]
          _ = (1 + (n - 1)) • P0 := (add_zsmul (m := (1 : ℤ)) (n := n - 1) P0).symm
          _ = n • P0 := by rw [show 1 + (n - 1) = n by ring]
      have hminus : P0 - WeierstrassCurve.Affine.Point.some u v hQns = -( (n - 2) • P0) := by
        rw [← hQ, sub_eq_add_neg, ← neg_zsmul]
        calc P0 + ((- (n - 1)) • P0) = (1 : ℤ) • P0 + ((- (n - 1)) • P0) := by rw [one_zsmul]
          _ = (1 + (- (n - 1))) • P0 := (add_zsmul (m := (1 : ℤ)) (n := - (n - 1)) P0).symm
          _ = (2 - n) • P0 := by rw [show 1 + (- (n - 1)) = 2 - n by ring]
          _ = -( (n - 2) • P0) := by rw [show 2 - n = -(n - 2) by ring, neg_zsmul]
      have hxminus : xCoord W (P0 - WeierstrassCurve.Affine.Point.some u v hQns) = some s := by
        rw [hminus, xCoord_neg, hR]
        rfl
      have hslopeVal : W.addX x u (W.slope x u y (W.negY u v)) = s := by
        have := hrec.2.1
        rw [hxminus] at this
        exact (Option.some.inj this).symm
      rw [← hplus, hrec.1]
      rw [hrec.2.2, hslopeVal, hs, hwQ, hu]
      rw [show 2 * y + W.a₁ * x + W.a₃ = W.evalDivisionPolynomial x y 2 by
        rw [WeierstrassCurve.evalDivisionPolynomial_two]]
      rw [hphi_nm1', phi_eval W h (n - 2), phi_eval W h n]
      congr 1
      field_simp [hψ_n, hψ_nm1, hψ_nm2]
      have heven := evalDivisionPolynomial_even W h (n - 1)
      have heven' : W.evalDivisionPolynomial x y (-2 + n * 2) * W.evalDivisionPolynomial x y 2 =
          W.evalDivisionPolynomial x y (-2 + n) ^ 2 * W.evalDivisionPolynomial x y (-1 + n) *
              W.evalDivisionPolynomial x y (1 + n) -
            W.evalDivisionPolynomial x y (-3 + n) * W.evalDivisionPolynomial x y (-1 + n) *
              W.evalDivisionPolynomial x y n ^ 2 := by
        simpa [show -2 + n * 2 = 2 * (n - 1) by ring, show -2 + n = n - 2 by ring,
          show -1 + n = n - 1 by ring, show 1 + n = n + 1 by ring,
          show -3 + n = n - 3 by ring, show n - 1 - 1 = n - 2 by ring,
          show n - 1 + 2 = n + 1 by ring, show n - 1 - 2 = n - 3 by ring,
          show n - 1 + 1 = n by ring] using heven
      linear_combination (norm := ring)
        (1 - (W.evalDivisionPolynomial x y n) ^ 2 *
          (W.evalDivisionPolynomial x y (-2 + n)) ^ 2) * heven'
      linear_combination (norm := ring) (-1 : K) * heven'

/-- Conditional general formula: if all positive `ψ_k(P)` are nonzero and the
point-level omega identity holds for all positive `k`, then the x-coordinate
formula holds for every nonzero `n`. -/
theorem xCoordinateFormula_of_omega
    (hψ : ∀ k : ℤ, 1 ≤ k → ∀ (x y : K) (h : W.Nonsingular x y),
      W.evalDivisionPolynomial x y k ≠ 0)
    (hω : ∀ k : ℤ, 1 ≤ k → S1372OmegaFormula W k) :
    ∀ n : ℤ, n ≠ 0 → S1372XCoordinateFormula W n := by
  have hpos : ∀ N : ℕ, 1 ≤ N → S1372XCoordinateFormula W (N : ℤ) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro hN
      rcases N with _ | _ | _ | N
      · omega
      · simpa using xCoordinateFormula_one W
      · simpa using xCoordinateFormula_two W
      · have hN3 : (3 : ℤ) ≤ (N + 3 : ℕ) := by omega
        intro x y h hne
        have hψloc : ∀ k : ℤ, 1 ≤ k → k ≤ (N + 3 : ℕ) + 1 →
            W.evalDivisionPolynomial x y k ≠ 0 := by
          intro k hk _
          exact hψ k hk x y h
        have hxm1 : xCoord W (((N + 3 : ℕ) - 1 : ℤ) •
            WeierstrassCurve.Affine.Point.some x y h) =
            some ((W.Φ ((N + 3 : ℕ) - 1)).eval x /
              (W.evalDivisionPolynomial x y ((N + 3 : ℕ) - 1)) ^ 2) := by
          have h1 := ih (N + 2) (by omega) (by omega)
          exact h1 x y h (hψ ((N + 3 : ℕ) - 1) (by omega) x y h)
        have hxm2 : xCoord W (((N + 3 : ℕ) - 2 : ℤ) •
            WeierstrassCurve.Affine.Point.some x y h) =
            some ((W.Φ ((N + 3 : ℕ) - 2)).eval x /
              (W.evalDivisionPolynomial x y ((N + 3 : ℕ) - 2)) ^ 2) := by
          have h1 := ih (N + 1) (by omega) (by omega)
          exact h1 x y h (hψ ((N + 3 : ℕ) - 2) (by omega) x y h)
        have hωloc : wCoord W (((N + 3 : ℕ) - 1 : ℤ) •
            WeierstrassCurve.Affine.Point.some x y h) =
            W.evalDivisionPolynomial x y (2 * (((N + 3 : ℕ) - 1 : ℤ))) /
              (W.evalDivisionPolynomial x y (((N + 3 : ℕ) - 1 : ℤ))) ^ 4 := by
          exact hω ((N + 3 : ℕ) - 1 : ℤ) (by omega) x y h
            (hψ ((N + 3 : ℕ) - 1) (by omega) x y h)
        exact xCoordinateFormula_step W ((N + 3 : ℕ) : ℤ) (by omega) x y h hψloc hxm1 hxm2 hωloc
  intro n hn
  rcases lt_or_gt_of_ne hn with hneg | hposn
  · have h1 : (1 : ℤ) ≤ -n := by omega
    have h2 : S1372XCoordinateFormula W (-n) := hpos (-n).natAbs (by omega)
    have h3 : ((-n).natAbs : ℤ) = -n := Int.natAbs_of_nonneg (by omega)
    rw [h3] at h2
    exact (xCoordinateFormula_neg_iff W n).mpr h2
  · exact hpos n.natAbs (by omega) |> fun h => by
      rwa [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at h

end LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual

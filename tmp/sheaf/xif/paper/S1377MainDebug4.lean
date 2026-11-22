import tmp.sheaf.xif.paper.S1377OmegaBase

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual

open Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1372XCoordinateFormulaActual
open WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve.Affine K)

/-! ## The simultaneous induction for the x-coordinate and the omega formula -/

/-- Simultaneous induction.  Assume the point-level division-polynomial
sequence is an elliptic net (S1372EllipticNetAtPoint).  Then, as long as
psi_1(P), ..., psi_{n+1}(P) are all nonzero, the x-coordinate formula
and the omega formula hold at n. -/
theorem xCoordinate_and_omega_of_ellipticNet {x y : K} (h : W.Nonsingular x y)
    (hnet : S1372EllipticNetAtPoint W x y)
    (n : ℤ) (hn : 1 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0) :
    xCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
      some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2) ∧
    wCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
      W.evalDivisionPolynomial x y (2 * n) /
        (W.evalDivisionPolynomial x y n) ^ 4 := by
  let P0 : W.Point := WeierstrassCurve.Affine.Point.some x y h
  have hmain : ∀ N : ℕ, 1 ≤ N →
      (∀ k : ℤ, 1 ≤ k → k ≤ (N : ℤ) + 1 → W.evalDivisionPolynomial x y k ≠ 0) →
      xCoord W ((N : ℤ) • P0) =
        some ((W.Φ (N : ℤ)).eval x / (W.evalDivisionPolynomial x y (N : ℤ)) ^ 2) ∧
      wCoord W ((N : ℤ) • P0) =
        W.evalDivisionPolynomial x y (2 * (N : ℤ)) /
          (W.evalDivisionPolynomial x y (N : ℤ)) ^ 4 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro hN hψN
      rcases N with _ | _ | _ | M
      · omega
      · constructor
        · rw [show ((0 + 1 : ℕ) : ℤ) = 1 by norm_num, one_zsmul]
          simp [P0, xCoord, WeierstrassCurve.Φ_one, WeierstrassCurve.evalDivisionPolynomial_one]
        · rw [show ((0 + 1 : ℕ) : ℤ) = 1 by norm_num, one_zsmul]
          simp [P0, wCoord, WeierstrassCurve.evalDivisionPolynomial_two,
            WeierstrassCurve.evalDivisionPolynomial_one]
      · have h2 : W.evalDivisionPolynomial x y 2 ≠ 0 := hψN 2 (by norm_num) (by norm_num)
        constructor
        · simpa using xCoordinateFormula_two W x y h h2
        · simpa using omegaFormula_two W h h2
      · let n : ℤ := ((M + 3 : ℕ) : ℤ)
        have hn3 : 3 ≤ n := by dsimp [n]; omega
        have hn1 : 1 ≤ n := by omega
        have hψn : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0 := hψN
        have hψM2 : ∀ k : ℤ, 1 ≤ k → k ≤ ((M + 2 : ℕ) : ℤ) + 1 →
            W.evalDivisionPolynomial x y k ≠ 0 := by
          intro k hk1 hk2
          exact hψN k hk1 (by dsimp [n]; push_cast at hk2 ⊢; omega)
        have hψM1 : ∀ k : ℤ, 1 ≤ k → k ≤ ((M + 1 : ℕ) : ℤ) + 1 →
            W.evalDivisionPolynomial x y k ≠ 0 := by
          intro k hk1 hk2
          exact hψN k hk1 (by dsimp [n]; push_cast at hk2 ⊢; omega)
        have hIH2 := ih (M + 2) (by omega) (by omega) hψM2
        have hIH1 := ih (M + 1) (by omega) (by omega) hψM1
        have hxm1 : xCoord W ((n - 1) • P0) =
            some ((W.Φ (n - 1)).eval x / (W.evalDivisionPolynomial x y (n - 1)) ^ 2) := by
          rw [show n - 1 = ((M + 2 : ℕ) : ℤ) by dsimp [n]; push_cast; ring]
          exact hIH2.1
        have hωm1 : wCoord W ((n - 1) • P0) =
            W.evalDivisionPolynomial x y (2 * (n - 1)) /
              (W.evalDivisionPolynomial x y (n - 1)) ^ 4 := by
          rw [show n - 1 = ((M + 2 : ℕ) : ℤ) by dsimp [n]; push_cast; ring]
          exact hIH2.2
        have hxm2 : xCoord W ((n - 2) • P0) =
            some ((W.Φ (n - 2)).eval x / (W.evalDivisionPolynomial x y (n - 2)) ^ 2) := by
          rw [show n - 2 = ((M + 1 : ℕ) : ℤ) by dsimp [n]; push_cast; ring]
          exact hIH1.1
        have hstep := xCoordinateFormula_step W n hn3 x y h hψn hxm1 hxm2 hωm1
        have hWn : W.evalDivisionPolynomial x y n ≠ 0 := hψn n (by omega) (by omega)
        have hWm : W.evalDivisionPolynomial x y (n - 1) ≠ 0 :=
          hψn (n - 1) (by omega) (by omega)
        have hWm2 : W.evalDivisionPolynomial x y (n - 2) ≠ 0 :=
          hψn (n - 2) (by omega) (by omega)
        have hW2 : W.evalDivisionPolynomial x y 2 ≠ 0 := hψn 2 (by omega) (by omega)
        rcases hnP : n • P0 with _ | ⟨X, Y, hB⟩
        · rw [hnP] at hstep
          simp [xCoord] at hstep
        · rw [hnP] at hstep
          have hX : X = (W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2 := by
            simpa [xCoord] using hstep
          rcases hmP : (n - 1) • P0 with _ | ⟨u, v, hA⟩
          · rw [hmP] at hxm1
            simp [xCoord] at hxm1
          · rw [hmP] at hxm1 hωm1
            have hu : u = (W.Φ (n - 1)).eval x /
                (W.evalDivisionPolynomial x y (n - 1)) ^ 2 := by
              simpa [xCoord] using hxm1
            have hwA : 2 * v + W.a₁ * u + W.a₃ =
                W.evalDivisionPolynomial x y (2 * (n - 1)) /
                  (W.evalDivisionPolynomial x y (n - 1)) ^ 4 := by
              simpa [wCoord] using hωm1
            set a : K := W.evalDivisionPolynomial x y n with ha_def
            set b : K := W.evalDivisionPolynomial x y (n - 1) with hb_def
            set c : K := W.evalDivisionPolynomial x y (n - 2) with hc_def
            set g : K := W.evalDivisionPolynomial x y 2 with hg_def
            set d : K := W.evalDivisionPolynomial x y (2 * n - 2) with hd_def
            set e : K := W.evalDivisionPolynomial x y (2 * n - 1) with he_def
            set f : K := W.evalDivisionPolynomial x y (2 * n) with hf_def
            set Bv : K := W.evalDivisionPolynomial x y (n - 3) with hBv_def
            set Ev : K := W.evalDivisionPolynomial x y (n + 1) with hEv_def
            set Fv : K := W.evalDivisionPolynomial x y (n + 2) with hFv_def
            have ha : a ≠ 0 := by rw [ha_def]; exact hWn
            have hb : b ≠ 0 := by rw [hb_def]; exact hWm
            have hc : c ≠ 0 := by rw [hc_def]; exact hWm2
            have hg : g ≠ 0 := by rw [hg_def]; exact hW2
            have hu_eq : u = (W.Φ (n - 1)).eval x / b ^ 2 := by
              rw [hu, hb_def]
            have hX_eq : X = (W.Φ n).eval x / a ^ 2 := by
              rw [hX, ha_def]
            have hwA_eq : 2 * v + W.a₁ * u + W.a₃ = d / b ^ 4 := by
              rw [hwA, hd_def, hb_def]
              congr 1
              ring
            sorry
  have hN : 1 ≤ n.natAbs := by
    have h0 : (0 : ℤ) ≤ n := by omega
    have h1 := Int.natAbs_of_nonneg h0
    omega
  have h := hmain n.natAbs hN (by
    intro k hk1 hk2
    rw [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at hk2
    exact hψ k hk1 hk2)
  rwa [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at h


end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
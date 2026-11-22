import tmp.sheaf.xif.paper.S1377OmegaBase

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
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
              rw [hwA, hd_def, hb_def, show 2 * (n - 1) = 2 * n - 2 by ring]
            have hphi_m := phi_eval W h (n - 1)
            have hphi_m' : (W.Φ (n - 1)).eval x = x * b ^ 2 - a * c := by
              rw [hb_def, hc_def, ha_def]
              simpa [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring] using hphi_m
            have hphi_n := phi_eval W h n
            have hphi_n' : (W.Φ n).eval x = x * a ^ 2 - Ev * b := by
              rw [ha_def, hb_def, hEv_def]
              simpa using hphi_n
            have hxu : x - u = a * c / b ^ 2 := by
              rw [hu_eq, hphi_m']
              field_simp [hb]
              ring
            have he_odd : e = Ev * b ^ 3 - c * a ^ 3 := by
              rw [he_def, hEv_def, hb_def, hc_def, ha_def]
              have hodd := evalDivisionPolynomial_odd' W h (n - 1)
              simpa [show 2 * (n - 1) + 1 = 2 * n - 1 by ring,
                show n - 1 + 2 = n + 1 by ring, show n - 1 - 1 = n - 2 by ring,
                show n - 1 + 1 = n by ring] using hodd
            have hXu : X - u = - e / (a ^ 2 * b ^ 2) := by
              rw [hX_eq, hu_eq, hphi_n', hphi_m', he_odd]
              field_simp [ha, hb]
              ring
            have hux : u ≠ x := by
              intro hux
              have h0 : x - u = 0 := by rw [hux]; ring
              rw [hxu] at h0
              exact (div_ne_zero (mul_ne_zero ha hc) (pow_ne_zero 2 hb)) h0
            have hsmul : n • P0 = (n - 1) • P0 + P0 := by
              rw [show n = (((M + 2) + 1 : ℕ) : ℤ) by dsimp [n]; push_cast; ring,
                show n - 1 = (((M + 2 : ℕ)) : ℤ) by dsimp [n]; push_cast; ring,
                natCast_zsmul, natCast_zsmul]
              exact AddMonoid.nsmul_succ (M + 2) P0
            have hplus : WeierstrassCurve.Affine.Point.some u v hA + P0 =
                WeierstrassCurve.Affine.Point.some X Y hB := by
              calc WeierstrassCurve.Affine.Point.some u v hA + P0
                  = (n - 1) • P0 + P0 := by rw [hmP]
                _ = n • P0 := hsmul.symm
                _ = WeierstrassCurve.Affine.Point.some X Y hB := hnP
            have hsum := WeierstrassCurve.Affine.Point.add_of_X_ne (W := W.toAffine)
              (x₁ := u) (x₂ := x) (y₁ := v) (y₂ := y) (h₁ := hA) (h₂ := h) hux
            have hXadd : W.addX u x (W.slope u x v y) = X := by
              change WeierstrassCurve.Affine.Point.some u v hA +
                  WeierstrassCurve.Affine.Point.some x y h =
                  WeierstrassCurve.Affine.Point.some X Y hB at hplus
              rw [hplus] at hsum
              exact (WeierstrassCurve.Affine.Point.some.inj hsum).1.symm
            have hrec := wCoord_add_of_X_ne W hA h hux
            rw [hplus, hXadd] at hrec
            have hwP : wCoord W (WeierstrassCurve.Affine.Point.some x y h) = g := by
              rw [hg_def, wCoord_some, WeierstrassCurve.evalDivisionPolynomial_two]
            have hwA' : wCoord W (WeierstrassCurve.Affine.Point.some u v hA) = d / b ^ 4 := by
              rw [wCoord_some]
              exact hwA_eq
            have hstep' : xCoord W (WeierstrassCurve.Affine.Point.some X Y hB) =
                some ((W.Φ n).eval x / a ^ 2) := by
              simpa [ha_def] using hstep
            constructor
            · exact hstep'
            · rw [hrec, hwP, hwA']
              rw [w_recursion_algebra ha hb hc hxu hXu]
              exact (omega_step_algebra (a := a) (b := b) (c := c) (d := d) (e := e)
                (f := f) (g := g) (Bv := Bv) (Ev := Ev) (Fv := Fv) ha hb hc hg (by
                rw [hf_def, hg_def, hb_def, ha_def, hFv_def, hc_def, hEv_def]
                simpa using evalDivisionPolynomial_even' W h n) (by
                rw [hd_def, hg_def, hc_def, hb_def, hEv_def, hBv_def, ha_def]
                have hev := evalDivisionPolynomial_even' W h (n - 1)
                simpa [show 2 * (n - 1) = 2 * n - 2 by ring,
                  show n - 1 - 1 = n - 2 by ring, show n - 1 + 1 = n by ring,
                  show n - 1 - 2 = n - 3 by ring, show n - 1 + 2 = n + 1 by ring] using hev)
                he_odd (by
                rw [hb_def, hc_def, hFv_def, ha_def, hBv_def, hEv_def, hg_def, he_def]
                have hrel := rel3_special W hnet n
                linear_combination hrel)).symm
  have hN : 1 ≤ n.natAbs := by
    have h0 : (0 : ℤ) ≤ n := by omega
    have h1 := Int.natAbs_of_nonneg h0
    omega
  have h := hmain n.natAbs hN (by
    intro k hk1 hk2
    rw [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at hk2
    exact hψ k hk1 hk2)
  rwa [Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ n)] at h



/-- **The exact algebraic input used by the induction.**  This is the
elliptic-sequence relation `Rel₃` for the evaluated sequence
`n ↦ ψₙ(P)`.  It is implied by Mathlib's `IsEllipticNet`
(`S1372EllipticNetAtPoint`), the unproved bridge in Mathlib. -/
def S1377Rel3AtPoint (x y : K) : Prop :=
  ∀ m n r : ℤ,
    W.evalDivisionPolynomial x y (m + n) * W.evalDivisionPolynomial x y (m - n) *
        W.evalDivisionPolynomial x y r ^ 2 =
      W.evalDivisionPolynomial x y (m + r) * W.evalDivisionPolynomial x y (m - r) *
          W.evalDivisionPolynomial x y n ^ 2 -
        W.evalDivisionPolynomial x y (n + r) * W.evalDivisionPolynomial x y (n - r) *
          W.evalDivisionPolynomial x y m ^ 2

/-- Mathlib's elliptic-net property implies the exact relation used above. -/
theorem S1377Rel3AtPoint_of_ellipticNet {x y : K}
    (h : S1372EllipticNetAtPoint W x y) : S1377Rel3AtPoint W x y :=
  fun m n r => rel3_of_ellipticNet W h m n r

/-! ## Corollaries: the precise reduction to the elliptic-net bridge

The theorem below isolates the only missing Mathlib input: the assertion that
the evaluated division-polynomial sequence n ↦ ψ_n(P) is an elliptic net.
The remaining hypothesis `hψ` is the intermediate nonvanishing condition
ψ_1(P), ..., ψ_{n+1}(P) ≠ 0 used by the induction. -/

/-- Pointwise x-coordinate formula from the elliptic-net bridge. -/
theorem xCoordinateFormula_of_ellipticNet {x y : K} (h : W.Nonsingular x y)
    (hnet : S1372EllipticNetAtPoint W x y) (n : ℤ) (hn : 1 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0) :
    xCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
      some ((W.Φ n).eval x / (W.evalDivisionPolynomial x y n) ^ 2) :=
  (xCoordinate_and_omega_of_ellipticNet W h hnet n hn hψ).1

/-- Pointwise omega formula from the elliptic-net bridge. -/
theorem omegaFormula_of_ellipticNet {x y : K} (h : W.Nonsingular x y)
    (hnet : S1372EllipticNetAtPoint W x y) (n : ℤ) (hn : 1 ≤ n)
    (hψ : ∀ k : ℤ, 1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0) :
    wCoord W (n • WeierstrassCurve.Affine.Point.some x y h) =
      W.evalDivisionPolynomial x y (2 * n) /
        (W.evalDivisionPolynomial x y n) ^ 4 :=
  (xCoordinate_and_omega_of_ellipticNet W h hnet n hn hψ).2

/-- The x-coordinate formula in the shape of `S1372XCoordinateFormula`, under
the elliptic-net bridge and the intermediate nonvanishing hypothesis. -/
theorem S1372XCoordinateFormula_of_ellipticNet
    (hnet : ∀ (x y : K), S1372EllipticNetAtPoint W x y)
    (n : ℤ) (hn : 1 ≤ n)
    (hψ : ∀ (x y : K) (h : W.Nonsingular x y) (k : ℤ),
      1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0) :
    S1372XCoordinateFormula W n := by
  intro x y h hne
  exact xCoordinateFormula_of_ellipticNet W h (hnet x y) n hn (hψ x y h)

/-- The omega formula in the shape of `S1372OmegaFormula`, under the
elliptic-net bridge and the intermediate nonvanishing hypothesis. -/
theorem S1372OmegaFormula_of_ellipticNet
    (hnet : ∀ (x y : K), S1372EllipticNetAtPoint W x y)
    (n : ℤ) (hn : 1 ≤ n)
    (hψ : ∀ (x y : K) (h : W.Nonsingular x y) (k : ℤ),
      1 ≤ k → k ≤ n + 1 → W.evalDivisionPolynomial x y k ≠ 0) :
    S1372OmegaFormula W n := by
  intro x y h hne
  exact omegaFormula_of_ellipticNet W h (hnet x y) n hn (hψ x y h)

#print axioms xCoordinate_and_omega_of_ellipticNet
#print axioms omegaFormula_two
#print axioms omega_step_algebra
#print axioms rel3_of_ellipticNet
#print axioms S1372OmegaFormula_of_ellipticNet

end LeanFormal.IUT.XiFPaper.S1377OmegaFormulaActual
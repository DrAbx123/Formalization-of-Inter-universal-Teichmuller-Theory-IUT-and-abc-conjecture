/- A3 route-conforming (3): membership criterion for the chart differential.

  Using `Mzk1G1OmegaFreeActual` (Omega_{R n/Q} is free of rank one, `omegaEquivO` with
  `omegaEquivO omegaForm = 1`, `Phi_apply : Phi a = a . omegaForm`) we prove
  `x in p . top  <->  omegaEquivO x in p`  and, since `Psi omegaForm = n` (n a unit in Q),
  `x in p . top  <->  Psi x in p`. This is the algebraic core for 'du not in p Omega';
  the scheme-level bridge `Ram (chartMorphism0 u) @ p <-> D u not in p Omega` and the
  arithmetic step at `x - t in p` remain registered obligations.
  Header RECON: donors reused are Mzk1G1OmegaFreeActual (Psi, Phi, phiEquiv, omegaEquivO,
  Psi_omegaForm, Phi_apply), Mzk1G1OmegaBasisActual (natCast_isUnit), Mzk1G1OmegaActual
  (dX, coordX, coordY). No duplicate constructions, chain rule already in Mathlib
  (Derivation.map_aeval, used in Mzk1G1A3ChartDiffActual).
  NOT route B2: this file concerns the implementation `psiFixed` (chart product prod (x-t)).
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1A3ChartDiffActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaBasisActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartDiffCriterionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaFreeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaBasisActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual

variable (n : Nat)

/-- **自由秩 1 的成员判据**：`x ∈ p • ⊤ ↔ (omegaEquivO x) ∈ p`。 -/
theorem mem_smul_top_iff (hn : 1 ≤ n) (p : Ideal (B n)) (x : Omega n) :
    x ∈ p • (⊤ : Submodule (B n) (Omega n)) ↔ (omegaEquivO n hn) x ∈ p := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (I := p)
      (N := (⊤ : Submodule (B n) (Omega n)))
      (p := fun x => (omegaEquivO n hn) x ∈ p) hx ?_ ?_
    · intro a ha m _
      show (omegaEquivO n hn) (a • m) ∈ p
      rw [map_smul, smul_eq_mul, mul_comm]
      exact p.mul_mem_left ((omegaEquivO n hn) m) ha
    · intro x y hx hy
      simpa using p.add_mem hx hy
  · intro hx
    have hPhi : (Phi n) ((omegaEquivO n hn) x) = x := by
      have := (phiEquiv n hn).apply_symm_apply x
      simpa [phiEquiv, omegaEquivO] using this
    rw [← hPhi, Phi_apply]
    have hmem : (omegaEquivO n hn) x • (omegaForm n) ∈
        p • (⊤ : Submodule (B n) (Omega n)) :=
      Submodule.smul_mem_smul (I := p)
        (N := (⊤ : Submodule (B n) (Omega n))) hx Submodule.mem_top
    simpa using hmem

/-- **`Psi` 版成员判据**（`n` 在 ℚ 中可逆）：`x ∈ p • ⊤ ↔ Psi x ∈ p`。 -/
theorem mem_smul_top_iff_Psi (hn : 1 ≤ n) (p : Ideal (B n)) (x : Omega n) :
    x ∈ p • (⊤ : Submodule (B n) (Omega n)) ↔ Psi n x ∈ p := by
  rw [mem_smul_top_iff n hn p x]
  have hunit : IsUnit (n : B n) := natCast_isUnit n hn
  have hPsi : Psi n x = ((omegaEquivO n hn) x) * (n : B n) := by
    have h := Psi_comp_Phi n hn ((omegaEquivO n hn) x)
    have h1 : (Phi n) ((omegaEquivO n hn) x) = x := by
      have := (phiEquiv n hn).apply_symm_apply x
      simpa [phiEquiv, omegaEquivO] using this
    rw [h1] at h
    exact h
  rw [hPsi, mul_comm]
  exact (Ideal.unit_mul_mem_iff_mem p hunit).symm

#print axioms mem_smul_top_iff
#print axioms mem_smul_top_iff_Psi


/-- 由 `x − t ∈ p` 与 `t^n ≠ 1` 推出 `y ∉ p`（Fermat 关系 + 素理想）。 -/
theorem chartY_notMem_of_chartX_sub (n : Nat) (hn : 1 ≤ n) (p : Ideal (R n)) (hp : p.IsPrime)
    {t : ℚ} (hxt : chartX n - algebraMap ℚ (R n) t ∈ p) (htn : t ^ n ≠ 1) :
    chartY n ∉ p := by
  have hxpow : chartX n ^ n - (algebraMap ℚ (R n) t) ^ n ∈ p := by
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (chartX n) (algebraMap ℚ (R n) t) n
    rw [hc, mul_comm]
    exact p.mul_mem_left c hxt
  have h_unit : IsUnit (algebraMap ℚ (R n) (1 - t ^ n)) := by
    have hne : (1 - t ^ n : ℚ) ≠ 0 := by
      intro h
      exact htn (by linarith)
    exact IsUnit.map (algebraMap ℚ (R n)) (isUnit_iff_ne_zero.mpr hne)
  have h1t : algebraMap ℚ (R n) (1 - t ^ n) ∉ p := by
    intro h
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p h h_unit)
  have hrel : chartX n ^ n + chartY n ^ n = 1 := chartX_pow_add_chartY_pow_eq_one n
  have hyn : chartY n ^ n ∉ p := by
    intro hy
    have h1 : (1 : R n) - chartX n ^ n ∈ p := by
      have : chartY n ^ n = 1 - chartX n ^ n := by linear_combination hrel
      rwa [this] at hy
    have : algebraMap ℚ (R n) (1 - t ^ n) ∈ p := by
      have hmap : algebraMap ℚ (R n) (1 - t ^ n) =
          (1 : R n) - (algebraMap ℚ (R n) t) ^ n := by
        simp [map_sub, map_pow, map_one]
      rw [hmap]
      have h2 : (1 : R n) - chartX n ^ n + (chartX n ^ n - (algebraMap ℚ (R n) t) ^ n) ∈ p :=
        p.add_mem h1 hxpow
      convert h2 using 2
      ring
    exact h1t this
  intro hy
  exact hyn (p.pow_mem_of_mem hy n (by omega))

/-- 由 `x − t ∈ p` 与 `g(t) ≠ 0` 推出 `g(x) ∉ p`。 -/
theorem aeval_notMem_of_value (n : Nat) (g : Polynomial ℚ) (p : Ideal (R n))
    (hp : p.IsPrime) {t : ℚ} (hxt : chartX n - algebraMap ℚ (R n) t ∈ p)
    (hval : Polynomial.eval t g ≠ 0) :
    Polynomial.aeval (chartX n) g ∉ p := by
  have hdvd : Polynomial.X - Polynomial.C t ∣ g - Polynomial.C (Polynomial.eval t g) :=
    Polynomial.X_sub_C_dvd_sub_C_eval
  obtain ⟨q, hq⟩ := hdvd
  have hcong : Polynomial.aeval (chartX n) g - algebraMap ℚ (R n) (Polynomial.eval t g) ∈ p := by
    have h1 : Polynomial.aeval (chartX n) g - algebraMap ℚ (R n) (Polynomial.eval t g) =
        Polynomial.aeval (chartX n) (g - Polynomial.C (Polynomial.eval t g)) := by
      simp [map_sub, map_one]
    have h2 : Polynomial.aeval (chartX n) (g - Polynomial.C (Polynomial.eval t g)) =
        Polynomial.aeval (chartX n) ((Polynomial.X - Polynomial.C t) * q) := by rw [hq]
    have h3 : Polynomial.aeval (chartX n) ((Polynomial.X - Polynomial.C t) * q) =
        (chartX n - algebraMap ℚ (R n) t) * Polynomial.aeval (chartX n) q := by
      rw [map_mul]
      congr 1
      simp [map_sub, map_one]
    rw [h1, h2, h3, mul_comm]
    exact p.mul_mem_left (Polynomial.aeval (chartX n) q) hxt
  have h_unit : IsUnit (algebraMap ℚ (R n) (Polynomial.eval t g)) := by
    exact IsUnit.map (algebraMap ℚ (R n)) (isUnit_iff_ne_zero.mpr hval)
  intro hg
  have : algebraMap ℚ (R n) (Polynomial.eval t g) ∈ p := by
    have := p.sub_mem hg hcong
    simpa using this
  exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p this h_unit)

#print axioms chartY_notMem_of_chartX_sub
#print axioms aeval_notMem_of_value

end LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartDiffCriterionActual
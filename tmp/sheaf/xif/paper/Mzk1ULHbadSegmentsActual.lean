/- hq/hd 的 per-p 系数（Lead 核对要求）:
  ① unramified bad p（p∉different support）：Σ_{w|p} f_w = [Ftpd:Q] ⇒ 系数 d_mod·(Σf/[Ftpd:Q]) = d_mod ≥1;
  ② ramified p 归 different 段：用 δ_w ≥ e_w − 1 ⇒ Σ_w δ_w f_w ≥ [Ftpd:Q] − Σ_w f_w，
     故 2d_mod·(Σ δ f/[Ftpd:Q]) ≥ 2d_mod(1−Σf/[Ftpd:Q])；若 p 分歧（Σ f ≤ [Ftpd:Q]/2）
     则 ≥ d_mod ≥1 ⇒ 2d_mod 的因子吸收 ramified p。
  本件只给纯实数系数引理（per-p），不含 support 事实（那是下件）。
  donor: mathlib nlinarith/div 代数。 -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadSegmentsActual

/-- unramified bad p: 系数 d_mod·(Σf/[Ftpd:Q]) = d_mod ≥1 覆盖 log p（d_mod≥1, log p≥0）。 -/
theorem perPrime_unramified (p dmod FtpdQ sumf : ℝ)
    (hdmod : 1 ≤ dmod) (hlogp : 0 ≤ Real.log p)
    (hsumf : sumf = FtpdQ) (hFtpdQ : 0 < FtpdQ) :
    Real.log p ≤ dmod * (sumf / FtpdQ * Real.log p) := by
  have hcoef : sumf / FtpdQ = 1 := by
    rw [hsumf, div_self (ne_of_gt hFtpdQ)]
  rw [hcoef, mul_one]
  nlinarith [hlogp, hdmod]

/-- ramified p（different 段）: δ≥e−1 ⇒ Σδf ≥ [Ftpd:Q]−Σf；若分歧则 2d_mod 系数 ≥ d_mod ≥1。 -/
theorem perPrime_ramified (dmod FtpdQ sumf sumdf : ℝ)
    (hdmod : 1 ≤ dmod) (hlogp : 0 ≤ Real.log p)
    (hFtpdQ : 0 < FtpdQ)
    (hδ : FtpdQ - sumf ≤ sumdf)      -- Σδf ≥ [Ftpd:Q] − Σf
    (hram : 2 * sumf ≤ FtpdQ) :       -- 分歧: Σf ≤ [Ftpd:Q]/2
    Real.log p ≤ (2 * dmod) * (sumdf / FtpdQ * Real.log p) := by
  have hcoef : 1 ≤ 2 * dmod * (sumdf / FtpdQ) := by
    have h1 : (2 * dmod) * ((FtpdQ - sumf) / FtpdQ) ≤ 2 * dmod * (sumdf / FtpdQ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right _ (le_of_lt hFtpdQ)
      linarith
    have h2 : (2 * dmod) * ((FtpdQ - sumf) / FtpdQ) = 2 * dmod * (1 - sumf / FtpdQ) := by
      field_simp
    have h3 : 1 ≤ 2 * dmod * (1 - sumf / FtpdQ) := by
      have hratio : sumf / FtpdQ ≤ 1 / 2 := by
        rw [div_le_iff (by linarith)]
        linarith
      nlinarith [hdmod, hratio, hFtpdQ]
    rw [h2] at h1
    linarith
  have hlogp' : 0 ≤ Real.log p := hlogp
  nlinarith [hcoef, hlogp']

#print axioms perPrime_unramified
#print axioms perPrime_ramified

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadSegmentsActual

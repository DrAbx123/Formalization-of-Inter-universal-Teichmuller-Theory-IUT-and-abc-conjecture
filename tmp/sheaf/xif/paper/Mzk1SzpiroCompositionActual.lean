/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # B10 (abc): Szpiro composition — paper verdict + volume upper bound -/

/- Composition of hull's Szpiro interface shape
  `(hc : 0<c) (hVup : V <= 6c*logdf + C0) (hSS : c*logq <= V) : logq <= 6*logdf + C0/c`
with the paper-normalized verdict `s*A <= V`, `A = logQ/(2l)` (lana absLogQ).
Records the arithmetic chain; does NOT prove the volume upper bound (hull's open gap),
does NOT prove lana SSIneq/ABC. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SzpiroCompositionActual

theorem szpiro6_of_verdict_and_volumeUpper {s A V c logdf C0 logQ l : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hl : 0 < l)
    (hverdict : s * A ≤ V) (hVup : V ≤ 6 * c * logdf + C0)
    (hA : A = logQ / (2 * l)) :
    logQ ≤ (2 * l / s) * (6 * c * logdf + C0) := by
  have hchain : s * A ≤ 6 * c * logdf + C0 := le_trans hverdict hVup
  have h2l : (0 : ℝ) < 2 * l := by linarith
  have hA2 : logQ = 2 * l * A := by
    rw [hA]
    field_simp [h2l.ne']
  have key : (2 * l * A) * s ≤ (6 * c * logdf + C0) * (2 * l) := by
    calc (2 * l * A) * s = (s * A) * (2 * l) := by ring
      _ ≤ (6 * c * logdf + C0) * (2 * l) :=
          mul_le_mul_of_nonneg_right hchain h2l.le
  rw [hA2, div_mul_eq_mul_div, le_div_iff₀ hs]
  simpa [mul_comm, mul_left_comm, mul_assoc] using key

theorem verdict_of_cancelled_deficit {s A sumLogMu : ℝ}
    (h : 0 ≤ sumLogMu) : s * A ≤ sumLogMu + s * A := by linarith

theorem deficit_nonpos_of_coeff_nonneg {s A sumLogMu : ℝ} (h : 0 ≤ sumLogMu) :
    s * A - (sumLogMu + s * A) ≤ 0 := by linarith

end LeanFormal.IUT.XiFPaper.Mzk1SzpiroCompositionActual

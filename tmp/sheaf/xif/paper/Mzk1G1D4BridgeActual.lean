import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
/-!
# D4 bridge: real absorption from the C4/D2 letters

Route §6.4 L613-638.  Inputs (all real, `λ`-independent since this is the per-`λ` arithmetic):
* C4: `(1/6 - 2/l^2) Q ≤ (1 + 12 d/l) S + 10 (e l + eta)` (david
  `uc_c4_actual_paper_letters`, 21:25:34);
* D2 bound: `l ≤ C0 √h log(2 C0 h)` (sophie/kurt, in progress);
* error: `h - Q ≤ C0 √h log(2 C0 h) + C0`;
* `Q ≤ h`, `S ≤ D + N`, `h ≤ l^2`, `0 < l`, nonnegativities.

Output: `h/6 ≤ (1 + C/√h)(D+N) + C√h log(2 C h) + C` with an explicit constant
`C = 12d + 2(10 e C0 + C0/6) + C0 + 2(10 eta + 2 + C0/6) + 1`.
This is the real-valued D4 input of `D1AnalyticInput.upper_estimate`; the actual inhabitant
still needs the C4/D2/error letters instantiated by david/kurt/sophie.
-/
/-! ## Scale convention (route §5.4 / §6.4, L623-630)

* `h` is the D1-side q-height, which in our formalization is the actual `jHeight`
  (`D1AnalyticInput.upper_estimate` uses `jHeight/6`);
* `Q` is the C4 q-pilot letter.  David's `qPilotMagnitudePaper_v2` is paper `log q`;
  `M_paper_v2 = qPilotMagnitudePaper_v2/(2*l)` (kurt §8 K-side is M-scale);
* C4's `A` is the q-scale RHS.  The boxed C4 is `c_l Q ≤ A`, `c_l = 1/6 - 2/l^2`,
  hence `Q/6 ≤ A + (2/l^2) Q`;
* this file is pure real algebra and does not itself mix scales: the consumer must
  pass `h` and `Q` in the *same* q-scale (`h = q-height`, `Q = log q`); if the C4 letter
  is `M = Q/(2l)`, multiply by `2l` before applying.  The factor-6 dictionary
  `jHeight = 6*lambdaHeight + O(1)` is D3 (`height_dictionary_deg`), applied outside.

-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.D4BridgeActual

def d4C (C0 d e eta : ℝ) : ℝ :=
  12 * d + 2 * (10 * e * C0 + C0 / 6) + C0 + 2 * (10 * eta + 2 + C0 / 6) + 1

set_option maxHeartbeats 800000 in
theorem d4_absorption (h Q S D N l C0 d e eta : ℝ)
    (hh : 1 ≤ h) (hQh : Q ≤ h) (hS0 : 0 ≤ S) (hSD : S ≤ D + N)
    (hlpos : 0 < l) (hl2 : h ≤ l ^ 2)
    (hlup : l ≤ C0 * Real.sqrt h * Real.log (2 * C0 * h))
    (herr : h - Q ≤ C0 * Real.sqrt h * Real.log (2 * C0 * h) + C0)
    (hC4 : (1 / 6 - 2 / l ^ 2) * Q ≤ (1 + 12 * d / l) * S + 10 * (e * l + eta))
    (hC0 : 0 ≤ C0) (hd : 0 ≤ d) (he : 0 ≤ e) (heta : 0 ≤ eta) :
    h / 6 ≤ (1 + d4C C0 d e eta / Real.sqrt h) * (D + N)
      + d4C C0 d e eta * Real.sqrt h * Real.log (2 * d4C C0 d e eta * h)
      + d4C C0 d e eta := by
  set C := d4C C0 d e eta with hC
  have hC1 : 1 ≤ C := by rw [hC]; unfold d4C; nlinarith
  have hC12 : 12 * d ≤ C := by rw [hC]; unfold d4C; nlinarith
  have hClog2 : 2 * (10 * e * C0 + C0 / 6) ≤ C := by rw [hC]; unfold d4C; nlinarith
  have hClog : 10 * e * C0 + C0 / 6 ≤ C / 2 := by linarith
  have hCC0 : C0 ≤ C := by rw [hC]; unfold d4C; nlinarith
  have hCconst2 : 2 * (10 * eta + 2 + C0 / 6) ≤ C := by rw [hC]; unfold d4C; nlinarith
  have hCconst : 10 * eta + 2 + C0 / 6 ≤ C / 2 := by linarith
  have hsqrt_pos : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by linarith)
  have hsqrt_ge1 : 1 ≤ Real.sqrt h := Real.one_le_sqrt.mpr hh
  have hC0pos : 0 < C0 := by
    rcases eq_or_lt_of_le hC0 with h0 | h0
    · rw [← h0] at hlup; simp at hlup; linarith
    · exact h0
  have hlogC0_pos : 0 < Real.log (2 * C0 * h) := by
    have h1 : 0 < C0 * Real.sqrt h * Real.log (2 * C0 * h) := lt_of_lt_of_le hlpos hlup
    have h2 : 0 < C0 * Real.sqrt h := mul_pos hC0pos hsqrt_pos
    rcases mul_pos_iff.mp h1 with ⟨_, hlog⟩ | ⟨hneg, _⟩
    · exact hlog
    · exact absurd h2 (not_lt.mpr hneg.le)
  have hlogC_nonneg : 0 ≤ Real.log (2 * C * h) := by
    apply Real.log_nonneg; nlinarith
  have hlog_mono : Real.log (2 * C0 * h) ≤ Real.log (2 * C * h) := by
    apply Real.log_le_log (by positivity); nlinarith
  have hs : Real.sqrt h ≤ l := by
    rw [← Real.sqrt_sq hlpos.le]; exact Real.sqrt_le_sqrt hl2
  have h12l : 12 * d / l ≤ 12 * d / Real.sqrt h := by
    exact div_le_div_of_nonneg_left (by linarith) hsqrt_pos hs
  have hcoef : (1 + 12 * d / l) * S ≤ (1 + C / Real.sqrt h) * (D + N) := by
    have hc1 : 1 + 12 * d / l ≤ 1 + C / Real.sqrt h := by
      have h1 : 12 * d / Real.sqrt h ≤ C / Real.sqrt h :=
        div_le_div_of_nonneg_right hC12 hsqrt_pos.le
      linarith
    exact mul_le_mul hc1 hSD hS0 (by positivity)
  have hQ6 : Q / 6 ≤ (1 + 12 * d / l) * S + 10 * (e * l + eta) + 2 := by
    have hsplit : Q / 6 = (1 / 6 - 2 / l ^ 2) * Q + (2 / l ^ 2) * Q := by ring
    have h2 : (2 / l ^ 2) * Q ≤ (2 / l ^ 2) * h := mul_le_mul_of_nonneg_left hQh (by positivity)
    have hl2pos : 0 < l ^ 2 := by positivity
    have h3 : (2 / l ^ 2) * h ≤ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hl2pos]; nlinarith
    linarith
  have herr6 : (h - Q) / 6 ≤ (C0 / 6) * Real.sqrt h * Real.log (2 * C0 * h) + C0 / 6 := by
    have h1 : (h - Q) / 6 ≤ (C0 * Real.sqrt h * Real.log (2 * C0 * h) + C0) / 6 :=
      div_le_div_of_nonneg_right herr (by norm_num)
    linarith
  have hmain : h / 6 ≤ (1 + 12 * d / l) * S + 10 * (e * l + eta)
      + 2 + ((C0 / 6) * Real.sqrt h * Real.log (2 * C0 * h) + C0 / 6) := by
    have hhsplit : h / 6 = Q / 6 + (h - Q) / 6 := by ring
    linarith [hhsplit, hQ6, herr6]
  have h10l : 10 * (e * l) ≤ 10 * e * C0 * (Real.sqrt h * Real.log (2 * C0 * h)) := by
    nlinarith [mul_le_mul_of_nonneg_left hlup he]
  have hlogcombo : 10 * (e * l) + (C0 / 6) * Real.sqrt h * Real.log (2 * C0 * h)
      ≤ (C / 2) * (Real.sqrt h * Real.log (2 * C * h)) := by
    have h4 : Real.sqrt h * Real.log (2 * C0 * h) ≤ Real.sqrt h * Real.log (2 * C * h) :=
      mul_le_mul_of_nonneg_left hlog_mono hsqrt_pos.le
    have hnc : 0 ≤ Real.sqrt h * Real.log (2 * C0 * h) := by positivity
    have hprod : (10 * e * C0 + C0 / 6) * (Real.sqrt h * Real.log (2 * C0 * h))
        ≤ (C / 2) * (Real.sqrt h * Real.log (2 * C * h)) :=
      mul_le_mul hClog h4 hnc (by positivity)
    have hleft : 10 * (e * l) + (C0 / 6) * Real.sqrt h * Real.log (2 * C0 * h)
        ≤ (10 * e * C0 + C0 / 6) * (Real.sqrt h * Real.log (2 * C0 * h)) := by
      nlinarith [h10l]
    linarith [hleft, hprod]
  have hbound : h / 6 ≤ (1 + C / Real.sqrt h) * (D + N)
      + C * (Real.sqrt h * Real.log (2 * C * h)) + C := by
    have h1 : h / 6 ≤ (1 + C / Real.sqrt h) * (D + N)
        + (C / 2) * (Real.sqrt h * Real.log (2 * C * h)) + C := by
      nlinarith [hmain, hcoef, hlogcombo, hCconst]
    have h2 : (C / 2) * (Real.sqrt h * Real.log (2 * C * h))
        ≤ C * (Real.sqrt h * Real.log (2 * C * h)) := by
      nlinarith [hsqrt_ge1, hlogC_nonneg, hC1]
    linarith
  simpa [mul_assoc] using hbound

#print axioms d4_absorption

/-- **C4 q-scale consumer** (Lead ruling 2026-11-17: `Q = h = jHeight`, no factor 6).
`hC4 : c_l Q ≤ (1+12d/l)S + 10(e l + eta)` with `Q = h`; `hSD : S ≤ D+N` is the
tripodal dictionary input (route L615-621, david `logDiff`/`hcond`), and
`hlup : l ≤ C0 √h log(2 C0 h)` is the D2 second bound. -/
theorem d4_of_c4_qscale (h S D N l C0 d e eta : ℝ)
    (hh : 1 ≤ h) (hS0 : 0 ≤ S) (hSD : S ≤ D + N)
    (hlpos : 0 < l) (hl2 : h ≤ l ^ 2)
    (hlup : l ≤ C0 * Real.sqrt h * Real.log (2 * C0 * h))
    (hlog : 0 ≤ C0 * Real.sqrt h * Real.log (2 * C0 * h))
    (hC4 : (1 / 6 - 2 / l ^ 2) * h ≤ (1 + 12 * d / l) * S + 10 * (e * l + eta))
    (hC0 : 0 ≤ C0) (hd : 0 ≤ d) (he : 0 ≤ e) (heta : 0 ≤ eta) :
    h / 6 ≤ (1 + d4C C0 d e eta / Real.sqrt h) * (D + N)
      + d4C C0 d e eta * Real.sqrt h * Real.log (2 * d4C C0 d e eta * h)
      + d4C C0 d e eta :=
  d4_absorption h h S D N l C0 d e eta hh le_rfl hS0 hSD hlpos hl2 hlup
    (by linarith) hC4 hC0 hd he heta

#print axioms d4_of_c4_qscale

/-- **INTERIM legacy-scale variant** (Lead 终裁 2026-11-17 (B): legacy 只作临时支线，不作终版；主线统一 v2/Mpaper_v2/λ 权).  If the
`Q-NORMALIZATION-AUDIT` rules that C3's legacy `Q_legacy` is the correct `Q` and that it
equals the D4 q-height `h`, this wrapper applies.  `hQ` is the scale-identification
obligation; without the audit it is *not* known (audit §4: legacy and v2 differ by
`f_{w|P} f_{P|b} e_b f_b/[F_mod:Q]`). -/
theorem d4_of_c4_qscale_legacy (h Qleg S D N l C0 d e eta : ℝ)
    (hQ : Qleg = h)
    (hh : 1 ≤ h) (hS0 : 0 ≤ S) (hSD : S ≤ D + N)
    (hlpos : 0 < l) (hl2 : h ≤ l ^ 2)
    (hlup : l ≤ C0 * Real.sqrt h * Real.log (2 * C0 * h))
    (hlog : 0 ≤ C0 * Real.sqrt h * Real.log (2 * C0 * h))
    (hC4 : (1 / 6 - 2 / l ^ 2) * Qleg ≤ (1 + 12 * d / l) * S + 10 * (e * l + eta))
    (hC0 : 0 ≤ C0) (hd : 0 ≤ d) (he : 0 ≤ e) (heta : 0 ≤ eta) :
    h / 6 ≤ (1 + d4C C0 d e eta / Real.sqrt h) * (D + N)
      + d4C C0 d e eta * Real.sqrt h * Real.log (2 * d4C C0 d e eta * h)
      + d4C C0 d e eta := by
  subst h
  exact d4_of_c4_qscale Qleg S D N l C0 d e eta hh hS0 hSD hlpos hl2 hlup hlog hC4 hC0 hd he heta

#print axioms d4_of_c4_qscale_legacy
end LeanFormal.IUT.XiFPaper.D4BridgeActual
end
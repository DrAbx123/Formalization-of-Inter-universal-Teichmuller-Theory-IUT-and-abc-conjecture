import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
/-!
# route §5.4.4 / IUT IV Thm 1.10 constants: the `2 log l + 56 ≤ (4/9) E_ar` bound

Paper (IUT-TEXT-THM110.md, pp. 22-24):
* `e_mod` is the maximal ramification index of `F_mod` over ℚ, so `1 ≤ e_mod`;
* `e*_mod = 2^12 · 3^3 · 5 · e_mod = 552960 · e_mod` (so `e*_mod ≥ 552960`);
* `η_prm` is the positive real number of Proposition 1.6;
* route §5.4 writes `E_ar = e* l + η_prm`.

Hence `2 log l + 56 ≤ (4/9) E_ar` for `l ≥ 5` is a purely numerical consequence:
`(4/9) E_ar ≥ (4/9)·552960·l ≥ 2l + 56 ≥ 2 log l + 56`.
This file proves that, with no analytic estimate assumed (only `log l ≤ l`).

Lead lane: H-T / P8-P (paper constants used by U-C hpaper).
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6HConstActual

/-- Paper constant `e*_mod = 2^12 · 3^3 · 5 · e_mod` (IUT IV Thm 1.10). -/
def eStarMod (eMod : ℕ) : ℕ := 2 ^ 12 * 3 ^ 3 * 5 * eMod

theorem eStarMod_ge {eMod : ℕ} (h : 1 ≤ eMod) : 552960 ≤ eStarMod eMod := by
  calc (552960 : ℕ) = 2 ^ 12 * 3 ^ 3 * 5 * 1 := by norm_num
    _ ≤ 2 ^ 12 * 3 ^ 3 * 5 * eMod := Nat.mul_le_mul_left _ h
    _ = eStarMod eMod := rfl

theorem eStarMod_cast_ge {eMod : ℕ} (h : 1 ≤ eMod) : (552960 : ℝ) ≤ (eStarMod eMod : ℝ) := by
  exact_mod_cast eStarMod_ge h

/-- Numerical bound `2 log l + 56 ≤ (4/9) E_ar` from the paper lower bound
`552960 · l ≤ E_ar` and `l ≥ 5`. -/
theorem two_log_add_56_le_four_ninths_of_lower {l E : ℝ} (hl : 5 ≤ l)
    (hE : 552960 * l ≤ E) :
    2 * Real.log l + 56 ≤ (4 / 9) * E := by
  have hl0 : (0 : ℝ) < l := by linarith
  have hlog : Real.log l ≤ l := by
    have := Real.log_le_sub_one_of_pos hl0
    linarith
  have hE' : (4 / 9 : ℝ) * (552960 * l) ≤ (4 / 9) * E := by
    apply mul_le_mul_of_nonneg_left hE
    norm_num
  have hbig : 2 * l + 56 ≤ (4 / 9 : ℝ) * (552960 * l) := by
    nlinarith
  linarith

/-- route §5.4.4: with `E_ar = e*_mod · l + η_prm` (`e_mod ≥ 1`, `η_prm ≥ 0`, `l ≥ 5`),
`2 log l + 56 ≤ (4/9) E_ar`. -/
theorem two_log_add_56_le_four_ninths_Ear {eMod : ℕ} (he : 1 ≤ eMod)
    {l η E : ℝ} (hl : 5 ≤ l) (hη : 0 ≤ η)
    (hE : E = (eStarMod eMod : ℝ) * l + η) :
    2 * Real.log l + 56 ≤ (4 / 9) * E := by
  have heR : (552960 : ℝ) ≤ (eStarMod eMod : ℝ) := eStarMod_cast_ge he
  have hl0 : (0 : ℝ) < l := by linarith
  have hlower : 552960 * l ≤ E := by
    rw [hE]
    nlinarith
  exact two_log_add_56_le_four_ninths_of_lower hl hlower

end LeanFormal.IUT.XiFPaper.Mzk1P6HConstActual

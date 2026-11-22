/- R5 (route §7.2-7.3 update): the scale-invariant boundary distance on `P1(L)`,
`rho([a:b]) = min(|a|, |b|, |a-b|) / max(|a|, |b|)` (Lead 23:49 evidence). It vanishes
exactly on the boundary `{[0:1], [1:0], [1:1]}` and is invariant under scaling `c != 0`,
so it can be used for a P1-valued `phi_L` without choosing a global affine chart.
REUSE: `Mzk1G1GKDeltaActual` (chordal/padic distances, polynomial route, donors only).
DEDUP: no scale-invariant rho distance existed in the tree. -/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoDistanceActual

variable {L : Type*} [NormedField L]

/-- The scale-invariant boundary distance `rho([a:b])` on the projective line: the minimum of
`|a|`, `|b|`, `|a-b|` divided by the maximum of `|a|`, `|b|`. It is zero exactly on the
boundary points `[0:1]`, `[1:0]`, `[1:1]`. -/
def rhoDist (a b : L) : ℝ :=
  min (min ‖a‖ ‖b‖) ‖a - b‖ / max ‖a‖ ‖b‖

theorem rhoDist_nonneg (a b : L) : 0 ≤ rhoDist a b := by
  unfold rhoDist
  have h1 : 0 ≤ min (min ‖a‖ ‖b‖) ‖a - b‖ :=
    le_min (le_min (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have h2 : 0 ≤ max ‖a‖ ‖b‖ := le_max_of_le_left (norm_nonneg _)
  exact div_nonneg h1 h2

theorem rhoDist_le_one (a b : L) : rhoDist a b ≤ 1 := by
  unfold rhoDist
  have hpos : (0 : ℝ) ≤ max ‖a‖ ‖b‖ := le_max_of_le_left (norm_nonneg _)
  rcases eq_or_lt_of_le hpos with h0 | hpos'
  · rw [← h0, div_zero]
    norm_num
  · rw [div_le_one hpos']
    calc min (min ‖a‖ ‖b‖) ‖a - b‖ ≤ min ‖a‖ ‖b‖ := min_le_left _ _
      _ ≤ max ‖a‖ ‖b‖ := min_le_max

end LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoDistanceActual
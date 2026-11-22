/- GK §7.3: boundary-distance functions `delta_i` (route L671-705), part 1: the local
distances to `{0,1,inf}` — archimedean (chordal on C) and nonarchimedean (normalized
p-adic) — with continuity and positivity away from the boundary.

REUSE SURVEY (2026-11-17, repo reconnaissance):
- `Mzk1G1DisjointFamilyActual`: `GKCompactInput`, `GKCompactInput.exists_delta0`,
  `uniform_positive_away`, `exists_boundary_avoiding`, `gluedBoundaryPreimage_eq` —
  the consumer interface and the E1 covering argument (NOT duplicated here).
- `Mzk1G1UniversalGKInputDocActual` (alan): GK input field semantics doc.
- `Mzk1G1PhiFixedLChart0Actual` / `Mzk1G1PhiFixedLChart0BoundaryActual` /
  `Mzk1G1PhiFixedLChartInfBoundaryActual` (emmy/andrew): chart-0/t-chart point formulas
  and boundary-membership criteria — the chart layer for `delta` (next batch).
- `Mzk1G1FermatOverlapActual` / `Mzk1G1FermatSecondChartActual`: chart ring relations
  (`chart0_relation`, `chartInf_relation`) — bridge from homogeneous coordinates.
- `Mzk1P1ProperActual.projectiveLineGlued_compactSpace` is Zariski-level only (not for
  the analytic topology; recorded to avoid misuse).
DEDUP CONCLUSION: no existing chordal/normalized boundary-distance donor in the repo
(grep over tmp/sheaf/xif/paper: only this file) — these local distances are new.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

noncomputable section
open Real
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKDeltaActual

section Archimedean

/-- Chordal distance from a complex number to `0`. -/
def chordalZero (z : ℂ) : ℝ := ‖z‖ / Real.sqrt (1 + ‖z‖ ^ 2)

/-- Chordal distance from a complex number to `1`. -/
def chordalOne (z : ℂ) : ℝ := ‖z - 1‖ / Real.sqrt (2 * (1 + ‖z‖ ^ 2))

/-- Chordal distance from a complex number to `inf` (the boundary point at infinity). -/
def chordalInf (z : ℂ) : ℝ := 1 / Real.sqrt (1 + ‖z‖ ^ 2)

/-- The archimedean boundary distance: the minimum chordal distance to `{0,1,inf}`. -/
def chordalBoundaryDist (z : ℂ) : ℝ := min (chordalZero z) (min (chordalOne z) (chordalInf z))

theorem continuous_chordalZero : Continuous chordalZero := by
  unfold chordalZero
  refine Continuous.div (by fun_prop) (by fun_prop) ?_
  intro z
  exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

theorem continuous_chordalOne : Continuous chordalOne := by
  unfold chordalOne
  refine Continuous.div (by fun_prop) (by fun_prop) ?_
  intro z
  exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

theorem continuous_chordalInf : Continuous chordalInf := by
  unfold chordalInf
  refine Continuous.div continuous_const (by fun_prop) ?_
  intro z
  exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

theorem continuous_chordalBoundaryDist : Continuous chordalBoundaryDist := by
  unfold chordalBoundaryDist
  exact continuous_chordalZero.min (continuous_chordalOne.min continuous_chordalInf)

theorem chordalZero_pos {z : ℂ} (hz : z ≠ 0) : 0 < chordalZero z := by
  unfold chordalZero
  have h1 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h2 : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  exact div_pos h1 h2

theorem chordalOne_pos {z : ℂ} (hz : z ≠ 1) : 0 < chordalOne z := by
  unfold chordalOne
  have h1 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have h2 : 0 < Real.sqrt (2 * (1 + ‖z‖ ^ 2)) := Real.sqrt_pos.mpr (by positivity)
  exact div_pos h1 h2

theorem chordalInf_pos (z : ℂ) : 0 < chordalInf z := by
  unfold chordalInf
  have h2 : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  exact div_pos one_pos h2

/-- The archimedean boundary distance is positive away from `{0,1}`. -/
theorem chordalBoundaryDist_pos {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    0 < chordalBoundaryDist z := by
  unfold chordalBoundaryDist
  exact lt_min (chordalZero_pos h0) (lt_min (chordalOne_pos h1) (chordalInf_pos z))

end Archimedean

section Nonarchimedean

variable {L : Type*} [TopologicalSpace L] [Sub L] [One L]

/-- The normalized nonarchimedean boundary distance to `{0,1,inf}`, expressed through a
norm-like function `n : L → ℝ` (the p-adic absolute value):
`min (min (n lam) (n (lam - 1))) 1 / max 1 (n lam)`. -/
def padicBoundaryDist (n : L → ℝ) (lam : L) : ℝ :=
  min (min (n lam) (n (lam - 1))) 1 / max 1 (n lam)

theorem continuous_padicBoundaryDist {n : L → ℝ} (hn : Continuous n)
    (hsub : Continuous fun lam : L => n (lam - 1)) :
    Continuous (padicBoundaryDist n) := by
  unfold padicBoundaryDist
  refine Continuous.div ((hn.min hsub).min continuous_const)
    (continuous_const.max hn) ?_
  intro lam
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- The nonarchimedean boundary distance is positive when the norm-like function is
positive at `lam` and `lam - 1`. -/
theorem padicBoundaryDist_pos {n : L → ℝ} {lam : L}
    (h0 : 0 < n lam) (h1 : 0 < n (lam - 1)) :
    0 < padicBoundaryDist n lam := by
  unfold padicBoundaryDist
  have hA : 0 < min (n lam) (n (lam - 1)) := lt_min h0 h1
  have hB : 0 < min (min (n lam) (n (lam - 1))) 1 := lt_min hA zero_lt_one
  have hmax : 0 < max 1 (n lam) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact div_pos hB hmax
end Nonarchimedean

#print axioms continuous_chordalBoundaryDist
#print axioms chordalBoundaryDist_pos
#print axioms continuous_padicBoundaryDist
#print axioms padicBoundaryDist_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1GKDeltaActual

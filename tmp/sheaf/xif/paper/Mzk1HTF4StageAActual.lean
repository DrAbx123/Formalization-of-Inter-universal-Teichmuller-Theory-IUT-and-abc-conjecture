import tmp.sheaf.xif.paper.Mzk1HT83F4PolyActual
import Mathlib.Tactic
/-!
# H-T F4 Stage A: divisor/effective-height algebra for `h_{E_i} ≤ r_i h_{O(1)} + C_i`

Route §8.3 (L752-774) construction: for each fixed boundary `E_i` pick through every
geometric point a line not containing `Y`, multiply over the finite Galois orbit, then over
the orbits to obtain a homogeneous polynomial `P_i` with `div(P_i|_Y) = E_i + F_i`
(`F_i ≥ 0` effective); a uniform lower bound for the fixed divisor height gives
`h_{E_i}(y) ≤ r_i h_{O(1)}(y) + C_i = κ_i h_{ω_Y}(y) + C_i`, `κ_i = r_i/(n−3)`.

## Reuse / donor check (2026-11-17)
* `Mzk1HT83F4PolyActual.RouteF4PolyData` / `routeF4_of_polyData` / `kappa_nonneg` /
  `kappa_eq_mul_inv` — arithmetic bridge already DONE; this file supplies the missing
  `hE_le` from the divisor relation (Stage A algebra), no new arithmetic.
* `Mzk1G1A5LineBundleIsoActual.a5_line_bundle` (A4 actual line bundle) is the consumer
  for the `hnorm` normalization `r_i h_{O(1)} = κ_i h_{ω_Y}`; kept as a field here.
* ported `tmp/external/ported/tauceti_belyi_rr/TauCeti/AlgebraicGeometry/WeilDivisor/*`
  and `flt_core` Riemann-Roch rows are the eventual donors for the scheme-level
  `div(P_i|_Y)`/effective-divisor height functoriality (Stage B; not imported here).

The remaining geometric obligations are explicit fields `hdiv`/`hF_le`/`hnorm`; they are
NOT proved in this file.  `F4` is not closed by this stage.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.HTF4StageAActual
open LeanFormal.IUT.XiFPaper.Mzk1HT83F4PolyActual

/-- Stage A data: the actual polynomial `P_i` (degree `r_i`), the divisor relation
`h_{E_i} = r_i h_{O(1)} + h_{F_i}` with `F_i ≥ 0`, the uniform bound `h_{F_i} ≤ C_i`, and
the A4 normalization `r_i h_{O(1)} = κ_i h_{ω_Y}`. -/
structure F4DivisorHeightData where
  P : ℕ → Polynomial ℚ
  n : ℝ
  n_gt_three : 3 < n
  hO1 : ℕ → ℝ
  hOmega : ℕ → ℝ
  hE : ℕ → ℝ
  C : ℕ → ℝ
  F : ℕ → ℝ
  F_nonneg : ∀ i, 0 ≤ F i
  C_nonneg : ∀ i, 0 ≤ C i
  /-- divisor additivity: `h_{E_i} = r_i h_{O(1)} + h_{F_i}` -/
  hdiv : ∀ i, hE i = ((P i).natDegree : ℝ) * hO1 i + F i
  /-- effective fixed divisor height is uniformly bounded by `C_i` -/
  hF_le : ∀ i, F i ≤ C i
  /-- A4 normalization `r_i h_{O(1)} = (r_i/(n−3)) h_{ω_Y}` -/
  hnorm : ∀ i, ((P i).natDegree : ℝ) * hO1 i =
    ((P i).natDegree : ℝ) / (n - 3) * hOmega i

/-- `κ_i = r_i/(n−3)`. -/
def F4DivisorHeightData.kappa (D : F4DivisorHeightData) (i : ℕ) : ℝ :=
  ((D.P i).natDegree : ℝ) / (D.n - 3)

theorem F4DivisorHeightData.kappa_nonneg (D : F4DivisorHeightData) (i : ℕ) :
    0 ≤ D.kappa i := by
  unfold F4DivisorHeightData.kappa
  exact div_nonneg (Nat.cast_nonneg _) (by linarith [D.n_gt_three])

theorem F4DivisorHeightData.kappa_eq_mul_inv (D : F4DivisorHeightData) (i : ℕ) :
    D.kappa i = ((D.P i).natDegree : ℝ) * (D.n - 3)⁻¹ := by
  unfold F4DivisorHeightData.kappa
  rw [div_eq_mul_inv]

/-- Stage A: the divisor relation plus effective-height bound gives
`h_{E_i} ≤ r_i h_{O(1)} + C_i` (before the `κ` normalization). -/
theorem F4DivisorHeightData.hE_le_r (D : F4DivisorHeightData) (i : ℕ) :
    D.hE i ≤ ((D.P i).natDegree : ℝ) * D.hO1 i + D.C i := by
  have h := D.hdiv i
  have hF := D.hF_le i
  linarith

/-- Stage A: F4 in `κ` form, `h_{E_i} ≤ κ_i h_{ω_Y} + C_i`. -/
theorem F4DivisorHeightData.hE_le_kappa (D : F4DivisorHeightData) (i : ℕ) :
    D.hE i ≤ D.kappa i * D.hOmega i + D.C i := by
  have hr := D.hE_le_r i
  have hn := D.hnorm i
  calc D.hE i ≤ ((D.P i).natDegree : ℝ) * D.hO1 i + D.C i := hr
    _ = D.kappa i * D.hOmega i + D.C i := by rw [hn]; rfl

/-- Convert Stage A data to the existing `RouteF4PolyData`; the `hE_le` field is now
proved from the divisor relation instead of assumed. -/
def F4DivisorHeightData.toPolyData (D : F4DivisorHeightData) : RouteF4PolyData where
  P := D.P
  n := D.n
  n_gt_three := D.n_gt_three
  hO1 := D.hO1
  hOmega := D.hOmega
  hE := D.hE
  C := D.C
  C_nonneg := D.C_nonneg
  hE_le := D.hE_le_r
  hnorm := D.hnorm

/-- **F4 Stage A**: Stage A data ⇒ `RouteF4Statement` (`h_{E_i} ≤ κ_i h_{ω_Y} + C_i`),
reusing `routeF4_of_polyData`.  The geometric inputs `hdiv`/`hF_le` remain explicit. -/
theorem routeF4_of_divisorHeight (D : F4DivisorHeightData) :
    RouteF4Statement D.toPolyData :=
  routeF4_of_polyData D.toPolyData

#print axioms F4DivisorHeightData.hE_le_r
#print axioms F4DivisorHeightData.hE_le_kappa
#print axioms routeF4_of_divisorHeight
end LeanFormal.IUT.XiFPaper.HTF4StageAActual
end
import tmp.external.ported.tauceti_belyi_rr.TauCeti.AlgebraicGeometry.WeilDivisor.Basic
import tmp.sheaf.xif.paper.Mzk1HT83F4PolyActual
import tmp.sheaf.xif.paper.Mzk1G1F8PiActual
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
/-!
# H-T F4 Stage B: actual divisor/height data for `div(P_i|_Y) = E_i + F_i`

Route §8.3 (L752-774): `P_i` homogeneous of degree `r_i`, `div(P_i|_Y) = E_i + F_i`
with `F_i ≥ 0`; the chart-0 height `h_{O_Y(1)}(y)` is the concrete
`Height.logHeight ![(φ x0), (φ x1), 1]` (F8 first equality, `Mzk1G1F8PiActual`), and
the divisor-height estimate is `h_{E_i} ≤ h_{div(P_i|_Y)} ≤ r_i h_{O(1)} + C_i`;
with the A4 normalization this gives `h_{E_i} ≤ κ_i h_{ω_Y} + C_i` (`κ_i = r_i/(n−3)`).

## Reuse / donor check (2026-11-17)
* ported `TauCeti/AlgebraicGeometry/WeilDivisor/Basic.lean` (Apache-2.0): `WeilDivisor`,
  `coeff`, `ofPoint`, `IsEffective`, `pushforward`, weighted degree — olean available
  (`ProbeWeilDivisorActual`); used here for `E_i`/`F_i` and `F_i ≥ 0`.
* `Mzk1HT83F4PolyActual.RouteF4PolyData`/`routeF4_of_polyData` — arithmetic consumer;
  `Mzk1HTF4StageAActual.F4DivisorHeightData` — Stage A divisor algebra.
* `Mzk1G1F8PiActual.f8_pi_height_chart0` (DONE 21:00:11): the concrete `hO1` chart-0
  height is `Height.logHeight ![(φ x0),(φ x1),1]`.
* `Mzk1G1A5LineBundleIsoActual.a5_line_bundle` (A4) supplies `hnorm` normalization.

**Explicit obligations (Stage B geometric content, not proved here)**:
1. the actual homogeneous `P_i` (line × Galois-orbit products) and `IsHomogeneous`/`totalDegree`;
2. `divOf (P i) = E i + F i` with `F i` effective (Weil divisor of the restricted section);
3. `hE i ≤ hDivP i` (monotonicity for the effective `F_i`);
4. `hDivP i ≤ r_i hO1 i + C i` (per-place `|P_i|_w ≤ C_w max|x|_w^{r_i}` + product formula);
5. ported `WeilDivisor/Order`/`FiniteSum`/`Degree` oleans are **not** built; the order/
   pushforward height functoriality donors are missing (owner: grace B3 / henry Y_n).

F4 is **not closed** by this stage: these are explicit fields, not theorems.
-/
noncomputable section
open MvPolynomial AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.HTF4StageBActual
open LeanFormal.IUT.XiFPaper.Mzk1HT83F4PolyActual
open LeanFormal.IUT.XiFPaper.F8PiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open TauCeti.AlgebraicGeometry

variable {k : Type*} [Field k] [NumberField k]

/-- Stage B: actual divisor/height data for the route §8.3 construction.
`hDivP i` is the height of `div(P_i|_Y)`, `E_i + F_i` its decomposition with `F_i`
effective, `hO1` the concrete chart-0 `O_Y(1)` height, and `hnorm` the A4 normalization. -/
structure F4ActualDivisorData (n : ℕ) where
  n_gt_three : 3 < (n : ℝ)
  φ : Chart0Ring n →+* k
  /-- homogeneous polynomials `P_i` of degree `r_i` -/
  P : ℕ → MvPolynomial (Fin 3) ℚ
  r : ℕ → ℕ
  homog : ∀ i, (P i).IsHomogeneous (r i)
  /-- points carrying Weil divisors (`E_i`, `F_i`) -/
  X : Type
  /-- the divisor of the restricted section `P_i|_Y` -/
  divP : ℕ → WeilDivisor X
  E : ℕ → WeilDivisor X
  F : ℕ → WeilDivisor X
  F_effective : ∀ i, WeilDivisor.IsEffective (F i)
  hdiv : ∀ i, divP i = E i + F i
  /-- the concrete chart-0 `O_Y(1)` height -/
  hO1 : ℕ → ℝ
  hO1_eq : ∀ i, hO1 i = Height.logHeight ![(φ (x0 n)), (φ (x1 n)), 1]
  hOmega : ℕ → ℝ
  hE : ℕ → ℝ
  C : ℕ → ℝ
  C_nonneg : ∀ i, 0 ≤ C i
  /-- height of `div(P_i|_Y)` -/
  hDivP : ℕ → ℝ
  /-- monotonicity: `E_i` is a subdivisor of `div(P_i|_Y)` with effective complement -/
  hE_le_hDivP : ∀ i, hE i ≤ hDivP i
  /-- route §8.3 height estimate `h_{div(P_i|_Y)} ≤ r_i h_{O(1)} + C_i` -/
  hDivP_le : ∀ i, hDivP i ≤ (r i : ℝ) * hO1 i + C i
  /-- A4 normalization `r_i h_{O(1)} = (r_i/(n−3)) h_{ω_Y}` -/
  hnorm : ∀ i, (r i : ℝ) * hO1 i = (r i : ℝ) / (n - 3) * hOmega i

/-- Stage B: `h_{E_i} ≤ r_i h_{O(1)} + C_i` from the divisor-height estimate. -/
theorem F4ActualDivisorData.hE_le_r {n : ℕ} (D : F4ActualDivisorData (k := k) n) (i : ℕ) :
    D.hE i ≤ (D.r i : ℝ) * D.hO1 i + D.C i := by
  have h1 := D.hE_le_hDivP i
  have h2 := D.hDivP_le i
  linarith

/-- Stage B: F4 in `κ` form, `h_{E_i} ≤ κ_i h_{ω_Y} + C_i`, `κ_i = r_i/(n−3)`. -/
theorem F4ActualDivisorData.hE_le_kappa {n : ℕ} (D : F4ActualDivisorData (k := k) n) (i : ℕ) :
    D.hE i ≤ (D.r i : ℝ) / ((n : ℝ) - 3) * D.hOmega i + D.C i := by
  have h1 := D.hE_le_r i
  have h2 := D.hnorm i
  calc D.hE i ≤ (D.r i : ℝ) * D.hO1 i + D.C i := h1
    _ = (D.r i : ℝ) / ((n : ℝ) - 3) * D.hOmega i + D.C i := by rw [h2]

/-- Stage B: `F4ActualDivisorData` ⇒ `RouteF4Statement` (with `P` as `0`, the κ form
carries the content). -/
theorem routeF4_of_actualDivisor {n : ℕ} (D : F4ActualDivisorData (k := k) n) :
    ∀ i, D.hE i ≤ (D.r i : ℝ) / ((n : ℝ) - 3) * D.hOmega i + D.C i :=
  fun i => D.hE_le_kappa i

#print axioms F4ActualDivisorData.hE_le_r
#print axioms F4ActualDivisorData.hE_le_kappa
#print axioms routeF4_of_actualDivisor
end LeanFormal.IUT.XiFPaper.HTF4StageBActual
end
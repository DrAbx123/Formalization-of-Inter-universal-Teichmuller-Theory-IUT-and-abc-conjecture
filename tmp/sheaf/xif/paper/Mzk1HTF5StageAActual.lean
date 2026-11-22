import tmp.sheaf.xif.paper.Mzk1G1F6EtaChoiceActual
import Mathlib.Tactic
/-!
# H-T F5 Stage A: `(1−ηκ)h_ω ≤ (1+η)D(L)+C` ⇒ F6 core with the route η choice

Route §8.4 (L776-806): D1 applied to `φ_i(y)` together with F1-F3 gives
`(1−η κ_i) h_ω(y) ≤ (1+η) D(L) + C`; taking `κ = max κ_i` and
`η = δ/(2(1+(1+δ)κ))` yields the F6 form `h_ω ≤ (1+δ)D(L) + C6`.
This file isolates the **real-arithmetic** part (`F5DerivationData` + η choice);
the analytic/height inputs (D1 actual `LocalHeightCriterion`, F1 transport, F2/F3,
κ normalization by A4) remain explicit fields / obligations (Stage B).

## Reuse / donor check (2026-11-17)
* `Mzk1G1F6EtaChoiceActual.etaChoice` / `etaChoice_mul_kappa_lt_one` /
  `etaChoice_ratio_le` / `etaChoice_const_absorption` — DONE 21:48:23; reused verbatim.
* `Mzk1G1F6EtaChoiceActual.routeF6_of_F1_to_F5_choice` (DONE) and
  `Mzk1G1F5F6ConsumeActual.f6_eta_choice_consumption` (DONE 00:55:18) consume the same
  arithmetic in the `RouteHTData` packaging; this file gives the interface-free core.
* `Mzk1HT84F4F5InterfaceActual.F5Statement` (NO INHABITANT) is the eventual consumer;
  its `hEi`/`hO1`/`lstar` letters are not used here (Stage B instantiates them).
* ported TauCeti `WeilDivisor`/`FunctionField/RiemannRoch` donors are for Stage B only.

F5 is **not closed** by this stage: `F5DerivationData.hF5` is an explicit hypothesis.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.HTF5StageAActual
open LeanFormal.IUT.XiFPaper.F6EtaChoiceActual

/-- Stage A data for the F5 ⇒ F6 arithmetic: the O(1)-height `hOmega`, the discriminant
term `DL ≥ 0`, the effective constant `C5`, the maximal `κ`, the route `δ`, the F5 core
inequality, and the route η choice. -/
structure F5DerivationData where
  hOmega : ℝ
  DL : ℝ
  C5 : ℝ
  hC5_nonneg : 0 ≤ C5
  kappaMax : ℝ
  delta : ℝ
  hDL_nonneg : 0 ≤ DL
  hkappa_nonneg : 0 ≤ kappaMax
  hdelta_pos : 0 < delta
  hdelta_le_one : delta ≤ 1
  /-- F5 core: `(1−ηκ) h_ω ≤ (1+η) D(L) + C` at the route η -/
  hF5 : (1 - etaChoice delta kappaMax * kappaMax) * hOmega ≤
    (1 + etaChoice delta kappaMax) * DL + C5

/-- The route η `= δ/(2(1+(1+δ)κ))`. -/
def F5DerivationData.eta (D : F5DerivationData) : ℝ := etaChoice D.delta D.kappaMax

theorem F5DerivationData.eta_mul_kappa_lt_one (D : F5DerivationData) :
    D.eta * D.kappaMax < 1 := by
  simpa [F5DerivationData.eta] using
    etaChoice_mul_kappa_lt_one D.hdelta_pos D.hdelta_le_one D.hkappa_nonneg

theorem F5DerivationData.eta_ratio_le (D : F5DerivationData) :
    (1 + D.eta) / (1 - D.eta * D.kappaMax) ≤ 1 + D.delta := by
  simpa [F5DerivationData.eta] using
    etaChoice_ratio_le D.hdelta_pos D.hdelta_le_one D.hkappa_nonneg

theorem F5DerivationData.eta_const_le (D : F5DerivationData) {C6 : ℝ}
    (hC6 : 2 * D.C5 ≤ C6) : D.C5 / (1 - D.eta * D.kappaMax) ≤ C6 := by
  simpa [F5DerivationData.eta] using
    etaChoice_const_absorption D.hdelta_pos D.hdelta_le_one D.hkappa_nonneg
      D.hC5_nonneg hC6

/-- **F5 Stage A ⇒ F6 core**: for `2 C5 ≤ C6`, `h_ω ≤ (1+δ)D(L) + C6`. -/
theorem f5_to_f6_core (D : F5DerivationData) {C6 : ℝ} (hC6 : 2 * D.C5 ≤ C6) :
    D.hOmega ≤ (1 + D.delta) * D.DL + C6 := by
  have hηκ : D.eta * D.kappaMax < 1 := D.eta_mul_kappa_lt_one
  have hratio : (1 + D.eta) / (1 - D.eta * D.kappaMax) ≤ 1 + D.delta := D.eta_ratio_le
  have hCabs : D.C5 / (1 - D.eta * D.kappaMax) ≤ C6 := D.eta_const_le hC6
  have hpos : 0 < 1 - D.eta * D.kappaMax := by linarith
  have h1 : (1 - D.eta * D.kappaMax) * D.hOmega ≤ (1 + D.eta) * D.DL + D.C5 := D.hF5
  have h1' : D.hOmega * (1 - D.eta * D.kappaMax) ≤
      (1 + D.eta) * D.DL + D.C5 := by
    rw [mul_comm]; exact h1
  have h2 : D.hOmega ≤ ((1 + D.eta) * D.DL + D.C5) / (1 - D.eta * D.kappaMax) :=
    (le_div_iff₀ hpos).mpr h1'
  have hsplit : ((1 + D.eta) * D.DL + D.C5) / (1 - D.eta * D.kappaMax) =
      ((1 + D.eta) / (1 - D.eta * D.kappaMax)) * D.DL +
        D.C5 / (1 - D.eta * D.kappaMax) := by
    field_simp [ne_of_gt hpos]
  rw [hsplit] at h2
  have hmul : ((1 + D.eta) / (1 - D.eta * D.kappaMax)) * D.DL ≤
      (1 + D.delta) * D.DL :=
    mul_le_mul_of_nonneg_right hratio D.hDL_nonneg
  linarith

/-- **F5 Stage A ⇒ F6 with the enlarged constant `max C6 (2 C5)`** (no explicit `2C5≤C6`). -/
theorem f5_to_f6_core_choice (D : F5DerivationData) (C6 : ℝ) :
    D.hOmega ≤ (1 + D.delta) * D.DL + max C6 (2 * D.C5) := by
  refine f5_to_f6_core D (le_max_right _ _)

#print axioms f5_to_f6_core
#print axioms f5_to_f6_core_choice
end LeanFormal.IUT.XiFPaper.HTF5StageAActual
end
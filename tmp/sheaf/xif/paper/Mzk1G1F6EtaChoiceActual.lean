import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1HT86F6InterfaceActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.F6EtaChoiceActual

open LeanFormal.IUT.XiFPaper.Mzk1HT86F6InterfaceActual

/-- Route lines 778-800 explicit choice `eta = delta / (2 (1 + (1+delta) kappa))`. -/
def etaChoice (delta kappa : ℝ) : ℝ := delta / (2 * (1 + (1 + delta) * kappa))

lemma etaChoice_pos {delta kappa : ℝ} (hδ0 : 0 < delta) (hδ1 : delta ≤ 1)
    (hκ0 : 0 ≤ kappa) : 0 < etaChoice delta kappa := by
  unfold etaChoice
  have hA : 0 < 2 * (1 + (1 + delta) * kappa) := by nlinarith
  exact div_pos hδ0 hA

lemma etaChoice_mul_denom {delta kappa : ℝ} (hδ0 : 0 < delta) (hδ1 : delta ≤ 1)
    (hκ0 : 0 ≤ kappa) :
    etaChoice delta kappa * (1 + (1 + delta) * kappa) = delta / 2 := by
  unfold etaChoice
  have hA : (2 * (1 + (1 + delta) * kappa)) ≠ 0 := by nlinarith
  field_simp [hA]

lemma etaChoice_mul_kappa_le_half {delta kappa : ℝ} (hδ0 : 0 < delta) (hδ1 : delta ≤ 1)
    (hκ0 : 0 ≤ kappa) : etaChoice delta kappa * kappa ≤ 1 / 2 := by
  unfold etaChoice
  have hA : 0 < 2 * (1 + (1 + delta) * kappa) := by nlinarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hA]
  nlinarith

lemma etaChoice_mul_kappa_lt_one {delta kappa : ℝ} (hδ0 : 0 < delta) (hδ1 : delta ≤ 1)
    (hκ0 : 0 ≤ kappa) : etaChoice delta kappa * kappa < 1 := by
  have h := etaChoice_mul_kappa_le_half hδ0 hδ1 hκ0
  linarith

lemma etaChoice_denom_pos {delta kappa : ℝ} (hδ0 : 0 < delta) (hδ1 : delta ≤ 1)
    (hκ0 : 0 ≤ kappa) : 0 < 2 * (1 + (1 + delta) * kappa) := by
  nlinarith

lemma etaChoice_ratio_le {delta kappa : ℝ} (hδ0 : 0 < delta) (hδ1 : delta ≤ 1)
    (hκ0 : 0 ≤ kappa) :
    (1 + etaChoice delta kappa) / (1 - etaChoice delta kappa * kappa) ≤ 1 + delta := by
  have hκhalf := etaChoice_mul_kappa_le_half hδ0 hδ1 hκ0
  have hden : 0 < 1 - etaChoice delta kappa * kappa := by linarith
  rw [div_le_iff₀ hden]
  have hA : etaChoice delta kappa * (1 + (1 + delta) * kappa) = delta / 2 :=
    etaChoice_mul_denom hδ0 hδ1 hκ0
  nlinarith

lemma etaChoice_const_absorption {delta kappa C5 C6 : ℝ} (hδ0 : 0 < delta)
    (hδ1 : delta ≤ 1) (hκ0 : 0 ≤ kappa) (hC5 : 0 ≤ C5) (hC6 : 2 * C5 ≤ C6) :
    C5 / (1 - etaChoice delta kappa * kappa) ≤ C6 := by
  have hκhalf := etaChoice_mul_kappa_le_half hδ0 hδ1 hκ0
  have hden : 0 < 1 - etaChoice delta kappa * kappa := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- **F6 without the three arithmetic hypotheses**: if additionally `0 ≤ kappa`,
`0 ≤ C5`, `2 C5 ≤ C6`, the eta choice discharges all three route hypotheses. -/
theorem routeF6_of_F1_to_F5' (D : RouteHTData) (deg : ℝ)
    (h5 : RouteF5Statement D) (hκ0 : 0 ≤ D.κmax)
    (hC5 : 0 ≤ D.C5) (hC6 : 2 * D.C5 ≤ D.C6) :
    RouteF6Statement D deg := by
  refine routeF6_of_F1_to_F5 D deg h5 ?_ ?_ ?_
  · simpa [routeEta, etaChoice] using
      etaChoice_mul_kappa_lt_one D.delta_pos D.delta_le_one hκ0
  · simpa [routeEta, etaChoice] using
      etaChoice_ratio_le D.delta_pos D.delta_le_one hκ0
  · simpa [routeEta, etaChoice] using
      etaChoice_const_absorption D.delta_pos D.delta_le_one hκ0 hC5 hC6

#print axioms etaChoice_pos
#print axioms etaChoice_mul_kappa_lt_one
#print axioms etaChoice_ratio_le
#print axioms etaChoice_const_absorption
#print axioms routeF6_of_F1_to_F5'

/-- F6 statement with an explicit constant (the route allows any `C_{n,δ}`). -/
def RouteF6StatementWith (D : RouteHTData) (deg : ℝ) (C6 : ℝ) : Prop :=
  deg ≤ D.n ^ 2 → D.hOmega ≤ (1 + D.delta) * D.DL + C6

/-- **F6 choice wrapper with the constant `max C6 (2 C5)`**: only `0 ≤ κmax` and
`0 ≤ C5` need to be supplied from the actual F5/error data; the original interface's
`C6` is kept and the needed bound `2 C5 ≤ C6` is replaced by enlarging the constant. -/
theorem routeF6_of_F1_to_F5_choice (D : RouteHTData) (deg : ℝ)
    (h5 : RouteF5Statement D) (hκ0 : 0 ≤ D.κmax) (hC5 : 0 ≤ D.C5) :
    RouteF6StatementWith D deg (max D.C6 (2 * D.C5)) := by
  intro hdeg
  have hηκ : routeEta D * D.κmax < 1 := by
    simpa [routeEta, etaChoice] using
      etaChoice_mul_kappa_lt_one D.delta_pos D.delta_le_one hκ0
  have hratio : (1 + routeEta D) / (1 - routeEta D * D.κmax) ≤ 1 + D.delta := by
    simpa [routeEta, etaChoice] using
      etaChoice_ratio_le D.delta_pos D.delta_le_one hκ0
  have hC6le : 2 * D.C5 ≤ max D.C6 (2 * D.C5) := le_max_right _ _
  have hCabs : D.C5 / (1 - routeEta D * D.κmax) ≤ max D.C6 (2 * D.C5) := by
    simpa [routeEta, etaChoice] using
      etaChoice_const_absorption D.delta_pos D.delta_le_one hκ0 hC5 hC6le
  have hpos : 0 < 1 - routeEta D * D.κmax := by linarith
  have h1 : (1 - routeEta D * D.κmax) * D.hOmega ≤ (1 + routeEta D) * D.DL + D.C5 := h5
  have h1' : D.hOmega * (1 - routeEta D * D.κmax) <=
      (1 + routeEta D) * D.DL + D.C5 := by
    rw [mul_comm]; exact h1
  have h2 : D.hOmega ≤ ((1 + routeEta D) * D.DL + D.C5) / (1 - routeEta D * D.κmax) :=
    (le_div_iff₀ hpos).mpr h1'
  have hsplit : ((1 + routeEta D) * D.DL + D.C5) / (1 - routeEta D * D.κmax) =
      ((1 + routeEta D) / (1 - routeEta D * D.κmax)) * D.DL +
        D.C5 / (1 - routeEta D * D.κmax) := by
    field_simp
  rw [hsplit] at h2
  have hmul : ((1 + routeEta D) / (1 - routeEta D * D.κmax)) * D.DL ≤
      (1 + D.delta) * D.DL :=
    mul_le_mul_of_nonneg_right hratio D.DL_nonneg
  linarith

#print axioms routeF6_of_F1_to_F5_choice

end LeanFormal.IUT.XiFPaper.F6EtaChoiceActual
end
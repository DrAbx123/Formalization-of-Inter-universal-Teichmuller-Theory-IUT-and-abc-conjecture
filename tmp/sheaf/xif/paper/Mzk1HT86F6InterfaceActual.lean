/- H-T §8.1-§8.4: route F1-F6 named statements (NO INHABITANT) + F6 reduction.

Route 行号（Lead 2026-11-17 裁决, coord route 原文）:
* F1 (§8.1, lines 709-771): h_{O(1)}(φ_i(y)) = h_{ω_Y}(y) + h_{E_i}(y) + O_i(1);
* F2 (§8.2): D(K) + N_D(φ_i(y)) ≤ D(L) + N_{E_i}(y) + C_i;
* F3: N_{E_i}(y) ≤ h_{E_i}(y) + C_i;
* F4 (§8.3): h_{E_i}(y) ≤ r_i h_{O_Y(1)}(y) + C_i = κ_i h_{ω_Y}(y) + C_i,  κ_i = r_i/(n-3);
* F5: (1 - ηκ_i) h_ω(y) ≤ (1+η) D(L) + C;
* F6 (§8.4, lines 800-808): ∀ y, [ℚ(y):ℚ] ≤ n² ⇒ h_{ω_Y}(y) ≤ (1+δ)D(ℚ(y)) + C_{n,δ};
* 证明链 (lines 778-800): F5 取 η = δ/(2(1+(1+δ)κ)), κ = max_i κ_i,
  (1+η)/(1-ηκ) ≤ 1+δ ⇒ F6.

本文件只给命名接口（NO INHABITANT）与 F6 的算术归约；几何/高度输入来自
HT81Interface 与 §8.2/8.3 的 conductor/different 数据（alan 的 batch1-4c）。 -/
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT86F6InterfaceActual

/-- Route §8.1-§8.4 的高度/导出量数据（NO INHABITANT；每条 Fi 的字母都在字段里，
provenance 见文件头 route 行号）。 -/
structure RouteHTData where
  I : Type
  [fintypeI : Fintype I]
  [nonemptyI : Nonempty I]
  /-- n (route 的固定整数; 度数界 [ℚ(y):ℚ] ≤ n²) -/
  n : ℝ
  n_gt_three : 3 < n
  /-- δ ∈ (0,1] -/
  delta : ℝ
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  /-- h_{O(1)}(φ_i(y)) -/
  hO1 : I → ℝ
  /-- h_{ω_Y}(y) -/
  hOmega : ℝ
  /-- h_{E_i}(y) -/
  hE : I → ℝ
  Oi : I → ℝ
  /-- D(K_i) -/
  DK : I → ℝ
  /-- N_D(φ_i(y)) -/
  ND : I → ℝ
  /-- N_{E_i}(y) -/
  NE : I → ℝ
  /-- D(L) -/
  DL : ℝ
  DL_nonneg : 0 ≤ DL
  C2 : I → ℝ
  C3 : I → ℝ
  /-- r_i = deg P_i (route F4 的实际多项式次数) -/
  r : I → ℝ
  C4 : I → ℝ
  /-- κ = max_i κ_i (κ_i = r_i/(n-3)) -/
  κmax : ℝ
  hκmax : ∀ i, r i / (n - 3) ≤ κmax
  C5 : ℝ
  C6 : ℝ

attribute [instance] RouteHTData.fintypeI RouteHTData.nonemptyI

/-- η = δ/(2(1+(1+δ)κ))（route lines 778-800 的显式构造）。 -/
def routeEta (D : RouteHTData) : ℝ :=
  D.delta / (2 * (1 + (1 + D.delta) * D.κmax))

/-- Route F1 (§8.1): h_{O(1)}(φ_i(y)) = h_{ω_Y}(y) + h_{E_i}(y) + O_i(1)。 -/
def RouteF1Statement (D : RouteHTData) : Prop :=
  ∀ i, D.hO1 i = D.hOmega + D.hE i + D.Oi i

/-- Route F2 (§8.2): D(K_i)+N_D(φ_i(y)) ≤ D(L)+N_{E_i}(y)+C_i。 -/
def RouteF2Statement (D : RouteHTData) : Prop :=
  ∀ i, D.DK i + D.ND i ≤ D.DL + D.NE i + D.C2 i

/-- Route F3: N_{E_i}(y) ≤ h_{E_i}(y)+C_i。 -/
def RouteF3Statement (D : RouteHTData) : Prop :=
  ∀ i, D.NE i ≤ D.hE i + D.C3 i

/-- Route F4 (§8.3): h_{E_i}(y) ≤ κ_i h_{ω_Y}(y)+C_i, κ_i = r_i/(n-3)。 -/
def RouteF4Statement (D : RouteHTData) : Prop :=
  ∀ i, D.hE i ≤ D.r i / (D.n - 3) * D.hOmega + D.C4 i

/-- Route F5: (1-ηκ)h_ω(y) ≤ (1+η)D(L)+C（η=routeEta D, κ=κmax）。 -/
def RouteF5Statement (D : RouteHTData) : Prop :=
  (1 - routeEta D * D.κmax) * D.hOmega ≤ (1 + routeEta D) * D.DL + D.C5

/-- Route F6 (§8.4, lines 800-808): [ℚ(y):ℚ] ≤ n² ⇒ h_{ω_Y}(y) ≤ (1+δ)D(L)+C_{n,δ}。 -/
def RouteF6Statement (D : RouteHTData) (deg : ℝ) : Prop :=
  deg ≤ D.n ^ 2 → D.hOmega ≤ (1 + D.delta) * D.DL + D.C6

/-- F6 的 route 等价陈述（deg = [ℚ(y):ℚ]）。 -/
def F6Statement (D : RouteHTData) (deg : ℝ) : Prop := RouteF6Statement D deg

/-- **F6 归约**（route lines 778-800 的算术）：F5 + η/κ 界 ⇒ F6。
显式构造 η = δ/(2(1+(1+δ)κ))；条件 (1+η)/(1-ηκ) ≤ 1+δ；常数 C5/(1-ηκ) ≤ C6。 -/
theorem routeF6_of_F1_to_F5 (D : RouteHTData) (deg : ℝ)
    (h5 : RouteF5Statement D)
    (hηκ : routeEta D * D.κmax < 1)
    (hratio : (1 + routeEta D) / (1 - routeEta D * D.κmax) ≤ 1 + D.delta)
    (hC : D.C5 / (1 - routeEta D * D.κmax) ≤ D.C6) :
    RouteF6Statement D deg := by
  intro hdeg
  have hpos : 0 < 1 - routeEta D * D.κmax := by linarith
  have h1 : (1 - routeEta D * D.κmax) * D.hOmega ≤
      (1 + routeEta D) * D.DL + D.C5 := h5
  have h1' : D.hOmega * (1 - routeEta D * D.κmax) ≤
      (1 + routeEta D) * D.DL + D.C5 := by
    rw [mul_comm]
    exact h1
  have h2 : D.hOmega ≤
      ((1 + routeEta D) * D.DL + D.C5) / (1 - routeEta D * D.κmax) :=
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

/-- route F6 ⇒ 论文 F6 形式（定义等价）。 -/
theorem f6_of_routeF6 (D : RouteHTData) (deg : ℝ) (h : RouteF6Statement D deg) :
    F6Statement D deg := h

/-- 论文 F6 形式 ⇒ route F6（定义等价）。 -/
theorem routeF6_of_f6 (D : RouteHTData) (deg : ℝ) (h : F6Statement D deg) :
    RouteF6Statement D deg := h

#print axioms routeF6_of_F1_to_F5
#print axioms f6_of_routeF6
#print axioms routeF6_of_f6

end LeanFormal.IUT.XiFPaper.Mzk1HT86F6InterfaceActual
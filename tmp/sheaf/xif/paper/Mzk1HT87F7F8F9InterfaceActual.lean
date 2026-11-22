/- H-T §8.5-§8.6 (route 原文 L810-863): F7/F8/F9 具名 Prop 接口 + 条件式组装。

* F7 (L828): D(L) <= log rad(abc) + C_n；
* F8 (L841): h(pi(y)) = n * h_{O_Y(1)}(y) + O(1) = n/(n-3) * h_omega(y) + O(2 log 2)
  (archimedean 因子 2; 这里用显式误差界 |err| <= 2 log 2)；
* F9 (L853): log c <= (1+eps) log rad(abc) + C_eps;
* routeF9_of_F6_to_F8 (L850-857): F6+F7+F8 (+高度运输) => F9（纯算术）；
* routeFrey_of_F9: 复用 Mzk1P8FreyAssemblyActual.abcConjecture_of_logConjecture
  (DONE 2026-11-15, 三公理) 把 F9 (ABCLogConjecture 形式) 接到 ABCConjecture。

NO INHABITANT inputs: F7/F8 的 D(L)、h(pi(y))、rad(abc) 等实际量由 §8.2/8.4 的
place/height 数据提供（alan batch1-4c, HT84 文件）；本文件只给陈述接口与算术组装。 -/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import tmp.sheaf.xif.paper.Mzk1P8FreyAssemblyActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT87F7F8F9InterfaceActual

/-! ## F7 (route L828) -/

/-- Route F7 的字母数据（NO INHABITANT）：D(L) = log|disc L|/[L:Q]、log rad(abc)、常数 C_n。 -/
structure RouteF7Data where
  DL : ℝ
  logRad : ℝ
  C : ℝ
  C_nonneg : 0 ≤ C

/-- Route F7 (L828): D(L) <= log rad(abc) + C_n。 -/
def RouteF7Statement (D : RouteF7Data) : Prop :=
  D.DL ≤ D.logRad + D.C

/-! ## F8 (route L841) -/

/-- Route F8 的字母数据（NO INHABITANT）：h(pi(y)) 的两种归一化等式 +
archimedean 误差界 |err| <= 2 log 2（archimedean 因子 2）。 -/
structure RouteF8Data where
  n : ℝ
  n_gt_three : 3 < n
  hPi : ℝ
  hO1 : ℝ
  hOmega : ℝ
  err : ℝ
  hPi_eq_O1 : hPi = n * hO1 + err
  hPi_eq_omega : hPi = n / (n - 3) * hOmega + err
  err_abs_le : |err| ≤ 2 * Real.log 2

/-- Route F8 (L841): h(pi(y)) = n*h_{O_Y(1)}(y)+err = n/(n-3)*h_omega(y)+err,
|err| <= 2 log 2。 -/
def RouteF8Statement (D : RouteF8Data) : Prop :=
  D.hPi = D.n * D.hO1 + D.err ∧
    D.hPi = D.n / (D.n - 3) * D.hOmega + D.err ∧
    |D.err| ≤ 2 * Real.log 2

/-! ## F9 (route L853) -/

/-- Route F9 (L853): log c <= (1+eps) log rad(abc) + C_eps（ABC 三元组上的对数界；
与 LeanFormal.IUT.ABCLogBound 逐字同形，便于 routeFrey_of_F9 复用）。 -/
def RouteF9Statement (epsilon C : ℝ) : Prop :=
  ∀ a b c : ℕ, LeanFormal.IUT.IsABCTriple a b c →
    Real.log (c : ℝ) ≤
      (1 + epsilon) * Real.log (LeanFormal.IUT.radical (a * b * c) : ℝ) + C

/-- (1+δ)^2 <= 1+ε, 当 δ = min 1 (ε/3) 且 ε > 0（route L853 的算术事实）。 -/
theorem one_add_delta_sq_le_one_add_eps {epsilon delta : ℝ} (heps : 0 < epsilon)
    (hdelta : delta = min 1 (epsilon / 3)) :
    (1 + delta) ^ 2 ≤ 1 + epsilon := by
  by_cases hle : epsilon ≤ 3
  · have hd : delta = epsilon / 3 := by
      rw [hdelta, min_eq_right]
      linarith
    rw [hd]
    nlinarith [heps]
  · have hd : delta = 1 := by
      rw [hdelta, min_eq_left]
      linarith
    rw [hd]
    nlinarith

/-- **F9 的逐三元组算术组装**（route L850-857）：F6+F7+F8+高度运输 =>
log c <= (1+ε) log rad + [(1+ε)C7 + (1+δ)C6 + C8 + C9]。 -/
theorem routeF9_pointwise_of_F6_to_F8
    {n epsilon delta hOmega DL logRad logC hPi C6 C7 C8 C9 : ℝ}
    (heps : 0 < epsilon) (hdelta : delta = min 1 (epsilon / 3))
    (hn : 4 ≤ n) (hdelta_n : n / (n - 3) ≤ 1 + delta)
    (hOmega_nn : 0 ≤ hOmega) (hDL_nn : 0 ≤ DL)
    (hF6 : hOmega ≤ (1 + delta) * DL + C6)
    (hF7 : DL ≤ logRad + C7)
    (hF8 : |hPi - n / (n - 3) * hOmega| ≤ C8)
    (hTransport : logC ≤ hPi + C9) :
    logC ≤ (1 + epsilon) * logRad +
      ((1 + epsilon) * C7 + (1 + delta) * C6 + C8 + C9) := by
  have hdelta_sq := one_add_delta_sq_le_one_add_eps heps hdelta
  have h1eps : 0 ≤ 1 + epsilon := by linarith
  have h1delta : 0 ≤ 1 + delta := by
    have : 0 ≤ delta := by
      rw [hdelta]
      exact le_min zero_le_one (by linarith)
    linarith
  have hpi_le : hPi ≤ n / (n - 3) * hOmega + C8 := by
    have := (abs_le.mp hF8).2
    linarith
  have hcoef_le : n / (n - 3) * hOmega ≤ (1 + delta) * hOmega :=
    mul_le_mul_of_nonneg_right hdelta_n hOmega_nn
  have hstep1 : hPi ≤ (1 + delta) * hOmega + C8 := by linarith
  have hstep2 : (1 + delta) * hOmega ≤ (1 + delta) * ((1 + delta) * DL + C6) :=
    mul_le_mul_of_nonneg_left hF6 h1delta
  have hexp : (1 + delta) * ((1 + delta) * DL + C6) =
      (1 + delta) ^ 2 * DL + (1 + delta) * C6 := by ring
  have hstep3 : (1 + delta) ^ 2 * DL ≤ (1 + epsilon) * DL :=
    mul_le_mul_of_nonneg_right hdelta_sq hDL_nn
  have hstep4 : (1 + epsilon) * DL ≤ (1 + epsilon) * (logRad + C7) :=
    mul_le_mul_of_nonneg_left hF7 h1eps
  have hexp2 : (1 + epsilon) * (logRad + C7) = (1 + epsilon) * logRad + (1 + epsilon) * C7 := by
    ring
  linarith

/-- **routeF9_of_F6_to_F8**（route L850-857）：若对每个 ABC 三元组存在 F6/F7/F8/运输的
字母数据（每条的 hOmega/DL/logC/hPi），则 RouteF9Statement 成立，常数
C_eps = (1+ε)C7 + (1+δ)C6 + C8 + C9。 -/
theorem routeF9_of_F6_to_F8
    (n epsilon delta C6 C7 C8 C9 : ℝ)
    (heps : 0 < epsilon) (hdelta : delta = min 1 (epsilon / 3))
    (hn : 4 ≤ n) (hdelta_n : n / (n - 3) ≤ 1 + delta)
    (hdata : ∀ (a b c : ℕ), LeanFormal.IUT.IsABCTriple a b c →
      ∃ (hOmega DL hPi : ℝ),
        0 ≤ hOmega ∧ 0 ≤ DL ∧ hOmega ≤ (1 + delta) * DL + C6 ∧
          DL ≤ Real.log (LeanFormal.IUT.radical (a * b * c) : ℝ) + C7 ∧
          |hPi - n / (n - 3) * hOmega| ≤ C8 ∧
          Real.log (c : ℝ) ≤ hPi + C9) :
    RouteF9Statement epsilon ((1 + epsilon) * C7 + (1 + delta) * C6 + C8 + C9) := by
  intro a b c habc
  obtain ⟨hOmega, DL, hPi, hOmega_nn, hDL_nn, hF6, hF7, hF8, hTransport⟩ := hdata a b c habc
  exact routeF9_pointwise_of_F6_to_F8 (n := n) (epsilon := epsilon) (delta := delta)
    (hOmega := hOmega) (DL := DL) (logRad := Real.log (LeanFormal.IUT.radical (a * b * c) : ℝ))
    (logC := Real.log (c : ℝ)) (hPi := hPi) (C6 := C6) (C7 := C7) (C8 := C8) (C9 := C9)
    heps hdelta hn hdelta_n hOmega_nn hDL_nn hF6 hF7 hF8 hTransport

/-- **routeFrey_of_F9**（复用 Mzk1P8FreyAssemblyActual.abcConjecture_of_logConjecture,
DONE 2026-11-15 三公理）：F9（对每个 ε>0 给常数 C_ε）⇒ ABCConjecture。 -/
theorem routeFrey_of_F9
    (h : ∀ epsilon : ℝ, 0 < epsilon → ∃ C : ℝ, RouteF9Statement epsilon C) :
    LeanFormal.IUT.ABCConjecture :=
  LeanFormal.IUT.XiFPaper.Mzk1P8FreyAssemblyActual.abcConjecture_of_logConjecture h

/-- F9 → ABC（ABCLogConjecture 形式）的显式转换（与 routeFrey_of_F9 等价, 便于引用）。 -/
theorem abcConjecture_of_routeF9
    (h : ∀ epsilon : ℝ, 0 < epsilon → ∃ C : ℝ, RouteF9Statement epsilon C) :
    LeanFormal.IUT.ABCConjecture :=
  routeFrey_of_F9 h

#print axioms one_add_delta_sq_le_one_add_eps
#print axioms routeF9_pointwise_of_F6_to_F8
#print axioms routeF9_of_F6_to_F8
#print axioms routeFrey_of_F9
#print axioms abcConjecture_of_routeF9

end LeanFormal.IUT.XiFPaper.Mzk1HT87F7F8F9InterfaceActual

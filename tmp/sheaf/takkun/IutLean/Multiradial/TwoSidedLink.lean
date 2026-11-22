import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.DisputedCore

/-!
# 2 つの ℝ の分離 — Θリンク比較の honest な定式化と空虚性定理

底本: Scholze–Stix "Why abc is still a conjecture" (2018) §2 / Mochizuki [Rpt2018] /
[IUT-III] Thm 3.11 → Cor 3.12 の架橋段階。

**方法論的訂正**: `Cor312.lean` の `PilotVolumeData` は単一の領域型 `Ω`・単一の体積 `vol` を
持ち、q標対象(受信側 Hodge 劇場)と Θ標対象(送信側)を**同一の空間・同一の正規化**の中で
比較する ―― これは係争点「送信側の `ℝ` と受信側の `ℝ` の同一視」を**構造の設計に前提として
含んで**いた。Thm 3.11 自体は(不定性込みの多輻的表示の主張として)比較的争いが少なく、
係争は **3.11 から 3.12 への架橋 = 2 つの `ℝ` の同一視**にある。

本モジュールは 2 つの側を型として分離し(`Send` / `Recv`、各々自前の体積正規化
`volS` / `volR`)、係争を**中立な 3 つの定理(トリレンマ)**として確定する:

1. **`relabeling_vacuous`(S–S 空虚性定理)**: リンクを体積保存の「単なる相対化」と読む
   (`IsRelabeling` = ℝ の同一視を transport で正当化する)なら、Cor 3.12 型不等式は
   **算術的入力なしに証明でき**、包の自明な性質「`vol(Θ標) ≤ vol(包)`」と**同値** ――
   すなわち「常に成り立つが無意味」(`0 ≤ 0` への崩壊、S–S の主張の形式化)。
2. **`link_not_isometric`(非等長定理)**: 各側の体積を各側の**算術的次数**で正規化する
   (q 非自明・Gauss 因子 `> 1`)なら、Θリンクは体積を**保てない** ―― `ℝ_send` と
   `ℝ_recv` は正当には同一視できない(スケーリングの不一致、ユーザー引用の論点の定理化)。
3. **`strict_collapse`**(`DisputedCore.lean`): 両方を同時に課す(単一空間 + 算術次数 +
   厳密包)と**矛盾**。

**トリレンマ**: (同一視 ⟹ 空虚) ∧ (算術次数 ⟹ 非等長) ∧ (両立 ⟹ 矛盾)。
ゆえに Cor 3.12 に内容を与える唯一の残された経路は、同一視によらず**受信側の正規化で**
転送された包の体積を上から評価すること(`TwoSidedSupply`)であり、係争
「望月は正しいか」は正確にこの供給の構成可能性 ―― [IUT-III] Thm 3.11 の多輻的転送 +
[IUT-IV] Prop 1.1–1.9 の対数体積計算が**受信側正規化で**遂行できるか ―― に確定する。
本形式化はこれを**裁定しない**(どちらの側も証明しない)。
-/

namespace IUT.Multiradial

universe u v w

/-- **Θリンク比較データ**(2 つの `ℝ` を分離した honest な設定): 送信側 `Send`(Θ側
Hodge 劇場の領域)と受信側 `Recv`(q側)は**別の型**であり、各々**自前の**体積正規化
`volS`/`volR` を持つ。Θリンク `link : Send → Recv` が両者を結び、`Θ標 ↦ q標` を定める。
単一空間 `Ω` を前提しない ―― 同一視は構造の外に置かれ、選択として明示される。 -/
structure ThetaLinkComparison where
  /-- 送信側(Θ側 Hodge 劇場)の領域。 -/
  Send : Type u
  [ordS : Preorder Send]
  /-- 受信側(q側 Hodge 劇場)の領域。**送信側とは別の型**。 -/
  Recv : Type v
  [ordR : Preorder Recv]
  /-- 送信側の対数体積(送信側 `ℝ` での正規化)。 -/
  volS : Send → ℝ
  volS_mono : Monotone volS
  /-- 受信側の対数体積(受信側 `ℝ` での正規化)。 -/
  volR : Recv → ℝ
  volR_mono : Monotone volR
  /-- 不定性群 `(Ind1)×(Ind2)`(送信側の多輻的表示に作用)。 -/
  Γ : Type w
  [group : Group Γ]
  [action : MulAction Γ Send]
  /-- Θ標対象(送信側)。 -/
  thetaPilot : Send
  /-- 正則包(送信側、不定性軌道全体を含む)。 -/
  hull : Send
  /-- 包は軌道全体を含む。 -/
  hull_spec : ∀ g : Γ, g • thetaPilot ≤ hull
  /-- q標対象(受信側)。 -/
  qPilot : Recv
  /-- **Θリンク**: 送信側の領域を受信側へ移す(単調)。 -/
  link : Send → Recv
  link_mono : Monotone link
  /-- Θリンクの定義: Θ標対象 ↦ q標対象。 -/
  link_pilot : link thetaPilot = qPilot

attribute [instance] ThetaLinkComparison.ordS ThetaLinkComparison.ordR
  ThetaLinkComparison.group ThetaLinkComparison.action

namespace ThetaLinkComparison

variable (T : ThetaLinkComparison.{u, v, w})

/-- **「同一視による読み」**: Θリンクが体積を保つ ―― `ℝ_send` と `ℝ_recv` を transport で
同一視する読み方(Scholze–Stix が「簡約すれば強制される」と論じ、Mochizuki が「不当」と
論じる、その同一視そのもの)。 -/
def IsRelabeling : Prop := ∀ x : T.Send, T.volR (T.link x) = T.volS x

/-- **S–S 空虚性定理**: 同一視の読み(`IsRelabeling`)のもとでは、Cor 3.12 型不等式
`volR(q標) ≤ volS(包)` は**算術的入力なしに**証明できる ―― `hull_spec` の `g = 1` の
場合だけから従い、q・高さ・Gauss 分布について**何の情報も含まない**。 -/
theorem relabeling_vacuous (h : T.IsRelabeling) :
    T.volR T.qPilot ≤ T.volS T.hull := by
  have h1 : T.volR T.qPilot = T.volS T.thetaPilot := by
    rw [← T.link_pilot]; exact h T.thetaPilot
  have h2 : T.volS T.thetaPilot ≤ T.volS T.hull := by
    have hg := T.hull_spec 1
    rw [one_smul] at hg
    exact T.volS_mono hg
  linarith

/-- **空虚性の内容**: 同一視の読みのもとで、Cor 3.12 型不等式は包の自明な性質
`vol(Θ標) ≤ vol(包)`(スラック `≥ 0`)と**同値** ―― 「常に成り立つが無意味な不等式」
(`0 ≤ 0` への崩壊)という Scholze–Stix の主張の厳密な形式化。 -/
theorem relabeling_inequality_iff (h : T.IsRelabeling) :
    (T.volR T.qPilot ≤ T.volS T.hull) ↔ (T.volS T.thetaPilot ≤ T.volS T.hull) := by
  have h1 : T.volR T.qPilot = T.volS T.thetaPilot := by
    rw [← T.link_pilot]; exact h T.thetaPilot
  rw [h1]

/-- **非等長定理**: 各側の体積を各側の**算術的次数**で正規化する(q 非自明:
`volR(q標) < 0`、Gauss 分布次数: `volS(Θ標) = factor·volR(q標)`, `factor > 1`)なら、
Θリンクは Θ標対象の体積を**保てない**: `volR(link(Θ標)) ≠ volS(Θ標)`。

すなわち**算術的正規化と体積保存の同一視は非両立** ―― 「送信側の `ℝ` と受信側の `ℝ` は
スケーリングが異なり、正当には同一視できない」の定理化。同一視を選べば空虚
(`relabeling_vacuous`)、算術次数を選べば同一視不能(本定理)―― これがトリレンマの 2 辺。 -/
theorem link_not_isometric (factor : ℝ) (hfac : 1 < factor)
    (hq : T.volR T.qPilot < 0)
    (hdeg : T.volS T.thetaPilot = factor * T.volR T.qPilot) :
    T.volR (T.link T.thetaPilot) ≠ T.volS T.thetaPilot := by
  rw [T.link_pilot, hdeg]
  intro hcontra
  nlinarith [mul_pos (sub_pos.2 hfac) (neg_pos.2 hq)]

/-- **歪み定理**(判定の核): Θリンクの体積歪みが定数 `c` で抑えられる(「近似的にでも
同一視できる」)なら、**高さそのものが `c/(factor−1)` で抑えられる**:
`|log q| ≤ c/(factor−1)`。

対偶: 高さが非有界な曲線族で ABC 型不等式を導くためには、**同一視の体積歪み自体が
`(factor−1)·|log q|`(= Gauss 利得全体、`l³` オーダー × 高さ)以上で増大**しなければ
ならない ―― 「同一視」と呼べる程度の(有界歪みの)対応では原理的に不可能。
望月側の主張は「テータ評価 `q ↦ q^{j²}` がまさにこの巨大な歪みを正準的に与える」であり、
Scholze–Stix 側の主張は「そのような歪みを持つ対応は正当な比較を与えない」である ――
係争の全内容がこの一つの定量的事実に集約される。 -/
theorem bounded_distortion_bounds_height (T : ThetaLinkComparison.{u, v, w})
    (factor c : ℝ) (hfac : 1 < factor)
    (hdeg : T.volS T.thetaPilot = factor * T.volR T.qPilot)
    (hdist : |T.volR (T.link T.thetaPilot) - T.volS T.thetaPilot| ≤ c) :
    -(T.volR T.qPilot) ≤ c / (factor - 1) := by
  rw [T.link_pilot, hdeg] at hdist
  have habs := abs_le.mp hdist
  have h1 : (factor - 1) * (-(T.volR T.qPilot)) ≤ c := by nlinarith [habs.1, habs.2]
  rw [le_div_iff₀ (by linarith : (0:ℝ) < factor - 1)]
  nlinarith [h1]

end ThetaLinkComparison

/-- **残余主張の 2 側版(係争の最終精密形)**: 同一視(`IsRelabeling`)に**よらず**、
受信側に転送された全可能像を含む受信側の包 `hullR` が存在し、その**受信側正規化での**
体積が `C_Θ·|log q|` で上から抑えられる比較データの存在。

これが Cor 3.12 に(空虚でない)内容を与える唯一の残された経路であり、
[IUT-III] Thm 3.11 の多輻的転送 + [IUT-IV] Prop 1.1–1.9 の対数体積計算が
**受信側の正規化のもとで**遂行できるか、という係争の核心そのもの。 -/
def TwoSidedSupply (factor CTheta : ℝ) : Prop :=
  ∃ (T : ThetaLinkComparison.{0, 0, 0}) (hullR : T.Recv),
    T.volR T.qPilot < 0 ∧
    T.volS T.thetaPilot = factor * T.volR T.qPilot ∧
    (∀ g : T.Γ, T.link (g • T.thetaPilot) ≤ hullR) ∧
    T.volR hullR ≤ CTheta * (-(T.volR T.qPilot))

/-- 2 側版供給から `C_Θ ≥ −1`(検証済みの鎖 `thm110_elementary_deduction` への接続)。
単一空間の同一視を前提せず、受信側の正規化のみで Cor 3.12 の帰結が得られることを確認
―― ゆえに残る問いは純粋に「`TwoSidedSupply` の算術的構成可能性」である。 -/
theorem twoSidedSupply_cTheta_ge_neg_one (factor CTheta : ℝ)
    (h : TwoSidedSupply factor CTheta) : -1 ≤ CTheta := by
  obtain ⟨T, hullR, hq, _, hcontain, hbound⟩ := h
  have h1 : T.qPilot ≤ hullR := by
    have hg := hcontain 1
    rwa [one_smul, T.link_pilot] at hg
  have h2 : T.volR T.qPilot ≤ T.volR hullR := T.volR_mono h1
  nlinarith [h2, hbound, hq]

end IUT.Multiradial

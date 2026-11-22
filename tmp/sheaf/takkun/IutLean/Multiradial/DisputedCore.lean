import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.Cor312
import tmp.sheaf.takkun.IutLean.Diophantine.Thm110

/-!
# 係争点の精密化 — Cor 3.12 の `containment` を巡る形式的分析

底本: [IUT-III] Thm 3.11, Cor 3.12 / Scholze–Stix "Why abc is still a conjecture" (2018) /
Mochizuki "Report on discussions..." (2018)。

`Cor312.lean` は Cor 3.12 の導出を `containment`(Thm 3.11 (iii) の多輻的両立性)に還元した。
本モジュールはこの係争点を**両陣営が合意できる形式的定理**として更に精密化する:

1. **`strict_collapse`(崩壊定理)**: 「厳密同一視」の追加仮定
   ―― (a) 不定性が体積を保つ(等長性、両陣営が合意)、(b) **正則包が Θ標対象自身の体積を
   超えない**(= Scholze–Stix の簡約「リンク沿いの ℝ のコピーの同一視」に対応)――
   のもとで、Gauss 分布次数(`factor > 1`)と `q` の非自明性から**矛盾が導出できる**。
   * Scholze–Stix はこれを「簡約すれば IUT は偽を導く、ゆえに議論に欠陥」と読み、
   * Mochizuki はこれを「ゆえに簡約(コピーの同一視)は不当であり、不定性・包の
     スラックが本質的」と読む。**崩壊事実そのものは両陣営が合意する数学**であり、
     ここでそれを `sorry` 無しの定理とする。

2. **`hull_exceeds_orbit`(スラックの所在)**: 不定性が体積を保つ限り、**軌道のどの元も
   正則包より真に小さい体積を持つ** ―― スラックは (Ind1),(Ind2) の軌道からは生じ得ず、
   **包の操作(log-Kummer 対応の (Ind3) 上半両立性による像の合併とその正則包)のみ**が
   源泉となる。係争は正確に「包がこのスラックを正当に生むか」に局在する。

3. **`slack_lower_bound`(スラックの定量的下界)**: 無矛盾な設定では
   `vol(包) − vol(Θ標) ≥ (factor − 1)·|log q|` ―― 不定性機構は **Gauss 分布の利得全体**を
   スラックとして負わなければならない。

4. **`MultiradialSupply`(残る主張の精密形)**: 係争の残余は「算術的データからの
   `PilotVolumeData` の供給で、包の体積が [IUT-IV] の `C_Θ` 公式(誤差項サイズ)で上から
   抑えられるもの」の存在に**正確に**還元される。`reflectionSupply` は抽象的枠組みとしては
   この供給が実現可能(枠組み自体は無矛盾)であることを示す ―― 係争は抽象枠組みの
   無矛盾性ではなく、**算術的実現**の存否にある。

本モジュールはどちらの陣営の主張も**証明しない**。係争を、形式的に検証可能な
単一の残余主張(`MultiradialSupply` の算術的インスタンス)へと厳密に絞り込む。
-/

namespace IUT.Multiradial

universe u v

/-! ## 1. 崩壊定理 ― 厳密同一視 + Gauss 次数 ⟹ 矛盾 -/

/-- **厳密同一視データ**(Scholze–Stix の簡約に対応する追加仮定を課した Cor 3.12 設定):
(a) 不定性の体積保存(等長性 ―― [IUT-III] Prop 3.9 (ii) 側でも主張され、両陣営が合意)、
(b) **厳密包**(包が Θ標対象自身の体積を超えない ―― リンク沿いの「ℝ のコピー」を同一視する
簡約の帰結)、(c) Gauss 分布次数 `vol(Θ標) = factor · vol(q標)`(`factor > 1`、
テータ値 `q^{j²}` の計算)、(d) `q` の非自明性(`|log q| > 0`、つまり `vol(q標) < 0`)。 -/
structure StrictPilotData extends PilotVolumeData.{u, v} where
  /-- (a) 不定性 `(Ind1),(Ind2)` は対数体積を保つ(等長性)。 -/
  vol_invariant : ∀ (g : Γ) (x : Ω), vol (g • x) = vol x
  /-- (b) **厳密包**: 正則包の体積は Θ標対象自身の体積を超えない
  (= Scholze–Stix の「コピーの同一視」簡約)。 -/
  hull_tight : vol hull ≤ vol thetaPilot
  /-- Gauss 分布次数因子(`l(l+1)/12` 型、`> 1`)。 -/
  factor : ℝ
  /-- 因子は `1` より大きい(`l ≥ 7` で `l(l+1)/12 ≥ 14/3 > 1`)。 -/
  factor_gt_one : 1 < factor
  /-- (c) Θ標対象の次数 = `factor ×` q標対象の次数(テータ値 `q^{j²}` の Gauss 分布計算)。 -/
  theta_degree : vol thetaPilot = factor * vol qPilot
  /-- (d) `q` は非自明(bad 素点の q-parameter は非単数、`|log q| > 0` ⟺ `vol(q標) < 0`)。 -/
  q_nontrivial : vol qPilot < 0

/-- **崩壊定理**: 厳密同一視データは存在しない(矛盾する)。

証明: Cor 3.12(`vol(q標) ≤ vol(包)`)と厳密包(`vol(包) ≤ vol(Θ標)`)と Gauss 次数
(`vol(Θ標) = factor·vol(q標)`)を連鎖すると `vol(q標) ≤ factor·vol(q標)`、すなわち
`0 ≤ (factor−1)·vol(q標) < 0`。∎

これは Scholze–Stix の崩壊論法([SS] §2.1)の形式化であると**同時に**、Mochizuki の
「コピーの同一視は不当」という主張([Rpt2018])の形式的根拠でもある ―― 両陣営が合意する
数学的事実。係争は「どの仮定を棄却すべきか」(`hull_tight` か、設定全体か)にある。 -/
theorem strict_collapse (S : StrictPilotData.{u, v}) : False := by
  have hc : S.vol S.qPilot ≤ S.vol S.hull := S.toPilotVolumeData.cor312
  nlinarith [hc, S.hull_tight, S.theta_degree,
    mul_pos (sub_pos.2 S.factor_gt_one) (neg_pos.2 S.q_nontrivial)]

/-! ## 2. スラックの所在 ― 軌道からは生じ得ない -/

/-- **スラックの所在**: 不定性が体積を保つ限り、Gauss 次数・`q` 非自明な任意の無矛盾設定で、
**軌道のどの元も正則包より真に小さい体積を持つ**:
`vol(g • Θ標) = vol(Θ標) = factor·vol(q標) < vol(q標) ≤ vol(包)`。

ゆえにスラック(包と Θ標の体積差)は `(Ind1),(Ind2)` の軌道からは**生じ得ず**、
log-Kummer 対応((Ind3) 上半両立性)による**像の合併とその正則包の操作のみ**が源泉となる。
係争は正確にこの一点 ―― 包の操作がこのスラックを正当に生むか ―― に局在する。 -/
theorem hull_exceeds_orbit (P : PilotVolumeData.{u, v}) (factor : ℝ)
    (hfac : 1 < factor) (hq : P.vol P.qPilot < 0)
    (hdeg : P.vol P.thetaPilot = factor * P.vol P.qPilot)
    (hinv : ∀ (g : P.Γ) (x : P.Ω), P.vol (g • x) = P.vol x) (g : P.Γ) :
    P.vol (g • P.thetaPilot) < P.vol P.hull := by
  have hc : P.vol P.qPilot ≤ P.vol P.hull := P.cor312
  have ho : P.vol (g • P.thetaPilot) = P.vol P.thetaPilot := hinv g P.thetaPilot
  nlinarith [hc, ho, hdeg, mul_pos (sub_pos.2 hfac) (neg_pos.2 hq)]

/-! ## 3. スラックの定量的下界 -/

/-- **スラックの定量的下界**: 無矛盾な設定では、正則包のスラックは Gauss 分布の利得全体
以上でなければならない: `(factor − 1)·|log q| ≤ vol(包) − vol(Θ標)`。

すなわち不定性・包の機構は、テータ値の Gauss 分布 `q^{j²}` が生む次数の広がり
(`≈ (l(l+1)/12 − 1)·|log q|`、`l³` オーダー)の**全体**をスラックとして負う。
[IUT-IV] Thm 1.10 の主張は「このスラックが同時に誤差項(different + 導手 + `e*·l`)で
上から抑えられる」こと ―― 下界(本定理)と上界(要供給)の間の窓が高さ不等式を生む。 -/
theorem slack_lower_bound (P : PilotVolumeData.{u, v}) (factor : ℝ)
    (hdeg : P.vol P.thetaPilot = factor * P.vol P.qPilot) :
    (factor - 1) * (-(P.vol P.qPilot)) ≤ P.vol P.hull - P.vol P.thetaPilot := by
  have hc : P.vol P.qPilot ≤ P.vol P.hull := P.cor312
  nlinarith [hc, hdeg]

/-! ## 4. 残る主張の精密形 -/

/-- **残る主張の精密形**(係争の全残余): 算術的 `q`(`vol(q標) < 0`)と Gauss 次数因子
`factor` を持ち、正則包の体積が `C_Θ·|log q|` で上から抑えられる(= [IUT-IV] Prop 1.1–1.9 の
対数体積計算の内容)`PilotVolumeData` の存在。

これが供給されれば `cTheta_ge_neg_one` → `thm110_elementary_deduction` の検証済みの鎖で
高さ不等式に到達する。`strict_collapse` により、供給は必然的に `hull_tight` を破る
(包は Θ標より真に大きい)形でのみ可能。 -/
def MultiradialSupply (factor CTheta : ℝ) : Prop :=
  ∃ P : PilotVolumeData.{0, 0}, P.vol P.qPilot < 0 ∧
    P.vol P.thetaPilot = factor * P.vol P.qPilot ∧
    P.negLogTheta ≤ CTheta * (-P.negLogQ)

/-- 供給があれば `C_Θ ≥ −1`(Cor 3.12 の帰結、検証済みの鎖への接続)。 -/
theorem supply_cTheta_ge_neg_one (factor CTheta : ℝ)
    (h : MultiradialSupply factor CTheta) : -1 ≤ CTheta := by
  obtain ⟨P, hq, _, hbound⟩ := h
  exact IUT.Diophantine.cTheta_ge_neg_one P CTheta (by
    simp only [PilotVolumeData.negLogQ]; linarith) hbound

/-! ## 5. 抽象枠組みの無矛盾性(witness) -/

/-- **反転作用による供給の witness**: `ℤˣ = {±1}` が `ℝ` に**アフィン反転**
`g • x := g·x + (3/2)(g−1)`(`1 • x = x`、`(−1) • x = −3−x`)で作用する。
`Θ標 = −2`、`q標 = −1 = (−1)•Θ標`(反転による像!)、`包 = −1`、`factor = 2`。
厳密包は破れている(`vol(包) = −1 > −2 = vol(Θ標)`)―― `strict_collapse` と整合。 -/
noncomputable def reflSupplyData : PilotVolumeData.{0, 0} where
  Ω := ℝ
  Γ := ℤˣ
  action :=
    { smul := fun g x => ((g : ℤ) : ℝ) * x + (3/2) * (((g : ℤ) : ℝ) - 1)
      one_smul := fun x => by
        show (((1 : ℤˣ) : ℤ) : ℝ) * x + (3/2) * ((((1 : ℤˣ) : ℤ) : ℝ) - 1) = x
        push_cast
        ring
      mul_smul := fun a b x => by
        show ((((a * b : ℤˣ) : ℤ)) : ℝ) * x + (3/2) * (((((a * b : ℤˣ) : ℤ)) : ℝ) - 1)
            = (((a : ℤ) : ℝ)) * ((((b : ℤ) : ℝ)) * x + (3/2) * ((((b : ℤ) : ℝ)) - 1))
              + (3/2) * ((((a : ℤ) : ℝ)) - 1)
        push_cast
        ring }
  vol := id
  vol_mono := monotone_id
  thetaPilot := -2
  qPilot := -1
  hull := -1
  hull_spec := fun g => by
    rcases Int.units_eq_one_or g with hg | hg <;> subst hg
    · show (((1 : ℤˣ) : ℤ) : ℝ) * (-2) + (3/2) * ((((1 : ℤˣ) : ℤ) : ℝ) - 1) ≤ -1
      norm_num
    · show ((((-1 : ℤˣ) : ℤ)) : ℝ) * (-2) + (3/2) * (((((-1 : ℤˣ) : ℤ)) : ℝ) - 1) ≤ -1
      norm_num
  containment := ⟨-1, by
    show (-1 : ℝ) ≤ (((-1 : ℤˣ) : ℤ) : ℝ) * (-2) + (3/2) * ((((-1 : ℤˣ) : ℤ) : ℝ) - 1)
    norm_num⟩

/-- **抽象枠組みの無矛盾性**: 供給命題 `MultiradialSupply 2 (−1)` は(厳密同一視を破る形で)
抽象的には実現可能。ゆえに `strict_collapse` は枠組み自体の矛盾ではなく、**厳密同一視の
仮定の帰結**である。係争の全残余は「**算術的データ**(実際の Hodge 劇場・対数殻・テータ値)
からの供給の存否」に確定する。 -/
theorem multiradialSupply_realizable : MultiradialSupply 2 (-1) := by
  refine ⟨reflSupplyData, ?_, ?_, ?_⟩
  · show (id (-1 : ℝ)) < 0; norm_num
  · show (id (-2 : ℝ)) = 2 * (id (-1 : ℝ)); norm_num
  · show (id (-1 : ℝ)) ≤ (-1) * (-(id (-1 : ℝ))); norm_num

end IUT.Multiradial

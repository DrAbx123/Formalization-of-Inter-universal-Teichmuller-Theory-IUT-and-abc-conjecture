import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.Thm311

/-!
# 転写の退化定理 — Phase R5(hull_bound の一般導出問題の最終形)

**Phase R の最終判定**: `hull_bound`(Thm 3.11 転写の残る唯一の義務)を、固定曲線の
数値的充足ではなく**一般に**導出できるか。本モジュールはこの問いに、形式化が到達し得る
最も精密な答えを与える:

## 主定理(全て標準公理のみ)

1. **`transcriptionOfCTheta`**: `cΘ ≥ −1` なら転写状態が構成できる(⟸ 方向の witness);
2. **`thm311Transcription_iff_cTheta`(転写レベルの退化定理、R5 の核)**:
   `Thm311Transcription A` の存在は `−1 ≤ A.cThetaFormula` と**同値**。
   すなわち **hull_bound の一般導出問題は、結論(cΘ ≥ −1 ―― ε-窓では Szpiro 型
   高さ不等式そのもの)と論理的に同値**であり、それ以上でも以下でもない;
3. **`lossless_hull_bound_iff`**: lossless な包(`vol(包) = −qVol` ―― R1–R4 の実機構
   [ノルム保存対数・深さ保存殻輸送・無損失 (Ind2)]が正直に与える包)の体積上界は
   `cΘ ≥ −1` と同値 ―― **実機構は退化同値を超える増分を一切供給しない**;
4. **`no_universal_transcription`**: 転写状態は数値データ空間上で**普遍的には充足不能**
   (反例 `unconstrainedData`)。ゆえに一様な供給(Cor 2.2 の前提)には、データが
   実際の楕円曲線から実現されるという幾何学的入力が本質的に必要。

## この定理群の意味(係争点への含意 ―― honest)

**確認されたこと(SS 側の構造)**: 非同一視の誠実な転写(`volS`/`volR` は別関数、比較は
リンク・Kummer 写像経由のみ)において、R1–R4 で実在化された全機構(p 進対数の
ノルム保存・exp 全単射・殻の深さ保存輸送・実体積)は lossless であり、Thm 3.11 の
義務の充足可能性を「結論の成立」以上に押し下げない。ε-窓では cΘ ≥ −1 ⟺ Szpiro 型
不等式ゆえ、**形式化可能だった全機構の範囲で、「Thm 3.11 ⟹ Cor 3.12 ⟹ Szpiro」の連鎖は
「Szpiro ⟺ Szpiro」に退化する** ―― Scholze–Stix の「誠実に正規化すると不等式は
無意味に崩壊する」という構造的主張の、この範囲での定理化である。

**確認されていないこと(望月側の残余)**: 未形式化の機構 ―― 分岐 different 項の実効化
(R6–R7)、`F_l⋆` 対称化平均が送信側因子 `arithFactor = l(l+1)/12` を受信側評価に
強制するという主張、(Ind1)–(Ind3) が不定性の全てであるという主張 ―― が lossless を
超える内容を生む可能性は、形式化されていない以上、**排除もされていない**。
本定理群が確定するのは「その未形式化機構の明示なしには導出が存在しない」ことであり、
挙証はその機構の側にある。
-/

namespace IUT.Multiradial

open IUT.Arithmetic

/-- **⟸ 方向の witness**: `cΘ ≥ −1` なら転写状態が構成できる(平行移動リンクの
ℝ-モデル ―― `adjudicationTest_iff_cTheta` の witness の転写版)。存在同値の片翼であり、
「出所を問わない存在命題は答えを書き込めば通る」ことの転写レベルの現れ。 -/
noncomputable def transcriptionOfCTheta (A : ArithmeticData) (hC : -1 ≤ A.cThetaFormula) :
    Thm311Transcription A :=
  { K :=
      { D := ℝ
        F := fun _ => ℝ
        log := fun _ => id
        kummer := fun _ _ => -A.qVol
        upperSemi := fun _ _ => le_refl _ }
    volR := id
    volR_mono := monotone_id
    volS := fun _ => A.arithFactor * (-A.qVol)
    volS_mono := monotone_const
    kummer0_mono := monotone_const
    thetaPilot := 0
    theta_vol := rfl
    hullR := -A.qVol
    hull_dominates := fun _ => le_refl _
    q_vol := rfl
    hull_bound := by
      change -A.qVol ≤ A.cThetaFormula * A.qVol
      nlinarith [A.qVol_pos, hC] }

/-- **転写レベルの退化定理(Phase R5 の核)**: 任意の算術データ `A` に対し、
Thm 3.11 転写状態の存在は `−1 ≤ cΘ` と**同値**。

`hull_bound` の一般導出問題は、こうして**結論そのものと論理的に同値**であることが
確定する ―― ε-窓(Cor 2.2 の regime)では `cΘ ≥ −1` は Szpiro 型高さ不等式に
ほかならないから、転写の一様な供給を仮定することは高さ不等式を仮定することと同値である。
(⟹ は `transcription_passes` + 退化定理、⟸ は witness 構成。) -/
theorem thm311Transcription_iff_cTheta (A : ArithmeticData) :
    Nonempty (Thm311Transcription A) ↔ -1 ≤ A.cThetaFormula := by
  constructor
  · rintro ⟨W⟩
    exact (ArithmeticData.adjudicationTest_iff_cTheta A).mp (transcription_passes A W)
  · intro hC
    exact ⟨transcriptionOfCTheta A hC⟩

/-- **lossless 包評価の同値**: 包の受信側体積が正確に `−qVol`(= R1–R4 の実機構
[ノルム保存対数・深さ保存殻輸送・無損失 (Ind2)・実 procession 正規化体積]が
正直に与える値)のとき、`hull_bound` の不等式は `cΘ ≥ −1` と同値。
**実機構は退化同値を超える増分を供給しない**ことの体積レベルの確定。 -/
theorem lossless_hull_bound_iff (A : ArithmeticData) {v : ℝ} (hv : v = -A.qVol) :
    v ≤ A.cThetaFormula * A.qVol ↔ -1 ≤ A.cThetaFormula := by
  subst hv
  constructor
  · intro h
    nlinarith [A.qVol_pos]
  · intro h
    nlinarith [A.qVol_pos]

/-- **普遍的充足の不能性**: 転写状態を全ての数値データに一様に供給することは
**形式的に不可能**(反例 = `unconstrainedData`: 高さが誤差項に比べ巨大)。
ゆえに Cor 2.2 の一様供給仮定を満たすには、「データが実際の楕円曲線から実現される」
という幾何学的入力(Szpiro の内容を持つ入力)が本質的に必要である。 -/
theorem no_universal_transcription :
    ¬ ∀ A : ArithmeticData, Nonempty (Thm311Transcription A) := by
  intro h
  obtain ⟨W⟩ := h unconstrainedData
  exact exam_not_universally_passable (transcription_passes _ W)

/-- **Phase R5 総括(判定定理)**: (i) 転写の存在は結論と同値(データごとの退化)、
かつ (ii) 普遍的供給は不能。この 2 つが、非同一視の誠実な形式化における
「Thm 3.11 → Cor 3.12」の到達点である。 -/
theorem transcription_degeneracy_verdict :
    (∀ A : ArithmeticData, Nonempty (Thm311Transcription A) ↔ -1 ≤ A.cThetaFormula)
    ∧ ¬ ∀ A : ArithmeticData, Nonempty (Thm311Transcription A) :=
  ⟨thm311Transcription_iff_cTheta, no_universal_transcription⟩

end IUT.Multiradial

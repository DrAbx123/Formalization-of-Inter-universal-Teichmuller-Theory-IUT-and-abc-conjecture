import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.TranscriptionDegeneracy

/-!
# Θ-包二分法 — Phase R7(分岐台帳込みの最終判定装置)

**R7 の問い**: R6 で形式化した分岐台帳([IUT-IV] Prop 1.1–1.3 の different 上界
`d = e−1`(順分岐)・`d ≤ e−1+e·v_p(e)`(暴分岐)と `LogShellRadius` の半径定数
`a, b`)は、R5 の退化定理(転写の存在 ⟺ `cΘ ≥ −1`)を変形させるか。

## 答え(本モジュールの定理群)

[IUT-III] Thm 3.11 (i)(ii) の**実際の主張**は、単なる包の存在ではなく
**多輻的表示の体積評価**: 「Θ-標対象の可能な像の包の受信側体積は、**送信側の Θ 体積
+ 分岐輸送の台帳 `L`** で上から抑えられる」である([IUT-IV] Thm 1.10 はこれと
containment から高さ不等式を出す)。これを **Θ-包ピン**(`theta_hull`)として転写に
追加した `ThetaHullTranscription` について:

1. **`thetaHull_forces_height`**([IUT-IV] Thm 1.10 の最終算術、論文に忠実):
   Θ-包ピン + containment ⟹ **高さ不等式 `(arithFactor−1)·qVol ≤ L`** が機械的に従う;
2. **`no_lossless_theta_hull`**: 台帳 `L = 0`(非分岐 lossless ―― R1–R4 で実在化した
   全機構が正直に与える値)では **Θ-包ピンは充足不能**。多輻的表示の主張は、
   高さと共に成長する台帳なしには**偽**である;
3. **`thetaHullTranscription_iff`(強化退化定理 = R7 の核)**: 任意の台帳 `L ≥ 0` に
   対し、Θ-包ピン付き転写の存在は
   **`(arithFactor−1)·qVol ≤ L`(高さ不等式)∧ `cΘ ≥ −1`** と同値。

## 最終判定への含意(honest)

R6 の台帳(論文 Prop 1.1–1.3 の形式化)は `L` の**値**を供給するのみであり、
**充足可能性の同値関係を一切変えない**: どんな精密な台帳で `L` を組んでも、
多輻的表示の主張(Θ-包ピン)の成立可能性は高さ不等式そのものと同値のまま
(2 の帰結として `L` は `(arithFactor−1)·qVol ≈ (l+1)/24·|log q|` 以上、すなわち
**高さと共に線形成長**しなければならず、それが実台帳で成り立つか否かの検証は
高さ不等式の検証と同値)。ゆえに:

* **確認(SS 側の構造、台帳込みの深さで)**: 論文の §1 計算([IUT-IV] Prop 1.1–1.4、
  R6 で検証済)を全て投入しても、「Thm 3.11 ⟹ Cor 3.12 ⟹ 高さ不等式」の連鎖の
  形式化可能な内容は「高さ不等式 ⟺ 高さ不等式」であり、結論の独立な導出を含まない;
* **未確認(望月側に残るもの)**: Θ-包ピン自体の、結論と同値でない導出 ――
  形式化された全 corpus(台帳込み)にそれは存在しない、が本定理群の主張であり、
  それを超える導出の明示は原理的に IUT 側にのみ可能である。
-/

namespace IUT.Multiradial

open IUT.Arithmetic

/-- **Θ-包ピン付き転写**([IUT-III] Thm 3.11 (i)(ii) の実際の主張の転写):
転写状態に**多輻的表示の体積評価** ―― 包の受信側体積は送信側 Θ 体積 + 分岐台帳 `L`
で抑えられる ―― を追加したもの。`L` は [IUT-IV] Prop 1.1–1.4 の d, a, b 台帳
(R6 `DifferentBound` + `LogShellRadius` で形式化済)から組まれる非負実数。 -/
structure ThetaHullTranscription (A : ArithmeticData) (L : ℝ)
    extends Thm311Transcription A where
  /-- 台帳は非負。 -/
  hL : 0 ≤ L
  /-- ★ **多輻的表示の体積評価(Θ-包ピン)**: 包の受信側体積 ≤ 送信側 Θ 体積 + 台帳。 -/
  theta_hull : volR hullR ≤ volS thetaPilot + L

/-- **高さ強制**([IUT-IV] Thm 1.10 の最終算術): Θ-包ピン + containment(基底 Kummer 像
は包に含まれる、機構から証明済)から**高さ不等式 `(arithFactor−1)·qVol ≤ L`** が
機械的に従う。`volS`/`volR` は別関数のまま ―― ℝ の同一視は現れない。 -/
theorem thetaHull_forces_height (A : ArithmeticData) {L : ℝ}
    (W : ThetaHullTranscription A L) :
    (A.arithFactor - 1) * A.qVol ≤ L := by
  have h1 : -A.qVol ≤ W.volR W.hullR := by
    rw [← W.q_vol]
    exact W.volR_mono (W.K.base_le_hull W.hull_dominates)
  have h2 := W.theta_hull
  rw [W.theta_vol, mul_neg] at h2
  have h3 : (A.arithFactor - 1) * A.qVol
      = A.arithFactor * A.qVol - A.qVol := by ring
  linarith

/-- **lossless では Θ-包ピンは充足不能**: 台帳 `L = 0`(R1–R4 の実機構
[ノルム保存対数・深さ保存殻輸送・無損失 (Ind2)]が正直に与える値)では、
多輻的表示の主張は**偽**(`arithFactor > 1`, `qVol > 0` ゆえ)。
Θ-包ピンの成立には**高さと共に成長する台帳**が必要である。 -/
theorem no_lossless_theta_hull (A : ArithmeticData) :
    ¬ Nonempty (ThetaHullTranscription A 0) := by
  rintro ⟨W⟩
  have h := thetaHull_forces_height A W
  have hF := A.arithFactor_gt_one
  nlinarith [A.qVol_pos]

/-- ⟸ 方向の witness: 高さ不等式 + cΘ 閾値から Θ-包ピン付き転写を構成。 -/
noncomputable def thetaHullTranscriptionOf (A : ArithmeticData) {L : ℝ} (hL : 0 ≤ L)
    (hht : (A.arithFactor - 1) * A.qVol ≤ L) (hC : -1 ≤ A.cThetaFormula) :
    ThetaHullTranscription A L :=
  { toThm311Transcription := transcriptionOfCTheta A hC
    hL := hL
    theta_hull := by
      change -A.qVol ≤ A.arithFactor * (-A.qVol) + L
      have h3 : (A.arithFactor - 1) * A.qVol
          = A.arithFactor * A.qVol - A.qVol := by ring
      rw [mul_neg]
      linarith }

/-- **強化退化定理(R7 の核 = 最終判定装置)**: 任意の台帳 `L ≥ 0` に対し、
**Θ-包ピン付き転写の存在 ⟺ 高さ不等式 `(arithFactor−1)·qVol ≤ L` ∧ `cΘ ≥ −1`**。

R6 で形式化した分岐台帳([IUT-IV] Prop 1.1–1.3)は `L` の値を供給するのみで、
この同値を**変えない** ―― 多輻的表示の主張の充足可能性は、どこまで台帳を精密化しても
**結論(高さ不等式)と同値のまま**である。 -/
theorem thetaHullTranscription_iff (A : ArithmeticData) {L : ℝ} (hL : 0 ≤ L) :
    Nonempty (ThetaHullTranscription A L) ↔
      ((A.arithFactor - 1) * A.qVol ≤ L ∧ -1 ≤ A.cThetaFormula) := by
  constructor
  · rintro ⟨W⟩
    exact ⟨thetaHull_forces_height A W,
      (thm311Transcription_iff_cTheta A).mp ⟨W.toThm311Transcription⟩⟩
  · rintro ⟨hht, hC⟩
    exact ⟨thetaHullTranscriptionOf A hL hht hC⟩

/-- **R7 総括(台帳込み最終判定)**: (i) lossless(`L = 0`)では多輻的表示の主張は
充足不能、(ii) 任意の台帳でその充足可能性は高さ不等式(∧ cΘ 閾値)と同値、
(iii) 転写自体の存在は cΘ 閾値と同値(R5)。分岐台帳の形式化(R6)を経ても、
形式化可能な全機構は結論の独立な導出を含まない。 -/
theorem lossy_degeneracy_verdict :
    (∀ A : ArithmeticData, ¬ Nonempty (ThetaHullTranscription A 0))
    ∧ (∀ (A : ArithmeticData) (L : ℝ), 0 ≤ L →
        (Nonempty (ThetaHullTranscription A L) ↔
          ((A.arithFactor - 1) * A.qVol ≤ L ∧ -1 ≤ A.cThetaFormula)))
    ∧ (∀ A : ArithmeticData,
        Nonempty (Thm311Transcription A) ↔ -1 ≤ A.cThetaFormula) :=
  ⟨no_lossless_theta_hull,
   fun A _ hL => thetaHullTranscription_iff A hL,
   thm311Transcription_iff_cTheta⟩

end IUT.Multiradial

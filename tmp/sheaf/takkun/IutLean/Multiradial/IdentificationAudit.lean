import Mathlib
import tmp.sheaf.takkun.IutLean.Multiradial.ThetaHullDichotomy
import tmp.sheaf.takkun.IutLean.Arithmetic.ExamAttempt

/-!
# 同一視監査 — Phase R8(SS バイアス検査: 同一視版 hull_bound は本当に通らないのか)

**監査の動機**: R5–R7 の判定(退化定理・Θ-包二分法)は Scholze–Stix の構造的主張を
定理として確認する形になった。これが「SS の枠組みに沿いすぎた設計の帰結」でないかを
検査する ―― 具体的には、既存 corpus が証明したのは
「同一視 + 両ピン(`theta_vol` ∧ `q_vol`)⟹ 矛盾」(`adjudication_not_relabeling`,
`strict_collapse`)までであり、**「同一視のもとで `hull_bound` 自体が充足可能か」は
未検証**だった。本モジュールはそれを直接検証する。

## 監査結果(本モジュールの定理群、全て標準公理のみ)

1. **`neg_arithFactor_le_cTheta`(無条件補題)**: `−l(l+1)/12 ≤ C_Θ` は**全ての**算術
   データで無条件に成立(恒等式 `C_Θ = P·X − arithFactor + 1/l`、`P·X ≥ 0`)。
2. **`identifiedTranscription_universal`**: 同一視版転写 `IdentifiedTranscription`
   (受信側ピン `q_vol` を同一視の法則 `volR ∘ kummer₀ = volS` = `IsRelabeling` の
   log-Kummer 基底版で**置換**したもの)は**普遍的に存在**する ―― 高さが誤差項に比べ
   巨大な反例データ `unconstrainedData`(非同一視版が証明可能に不可能な地点、
   `honest_fails_unconstrained`)でも通る(`identified_passes_unconstrained`)。
   **すなわち: 同一視版の `hull_bound` は「通らない」のではなく「無条件に通る」。**
3. **`identified_forces`**: 同一視版転写から containment + `hull_bound` で引き出せる
   結論は `−arithFactor ≤ C_Θ` のみ ―― これは 1 により**転写なしで証明済みの恒真命題**。
   同一視の道は開通しているが、その先に高さの情報(`−1 ≤ C_Θ`)は**存在しない**。
4. **`identified_qvol_incompatible`(不能性の正確な所在)**: 同一視の法則と受信側ピン
   `q_vol`(`volR(q標像) = −|log q|`)の同時成立は矛盾。**「同一視で通らない」ものは
   `hull_bound` ではなく `q_vol` ピン**であり、衝突する 2 つの値はどちらも論文内部の
   計算(送信側 = `theta_vol_derivation` のフロベニオイド内 Gaussian 次数、受信側 =
   Θリンクの定義 + q の受信側次数)である ―― SS の外部仮定ではない。
5. **`identified_lossless_theta_hull` / `identified_thetaHull_forces_only`**: Θ-包ピン
   (R7)も同一視版では**台帳 `L = 0` ですら充足可能**(⟷ 非同一視版の
   `no_lossless_theta_hull` は `L = 0` で充足不能)―― ただし高さ強制
   (`thetaHull_forces_height`)は `0 ≤ L` に退化する(SS の「0 ≤ 0 崩壊」の
   Θ-包ピンレベルでの正確な形)。

## バイアス監査の結論(honest)

形式化は同一視の道を**塞いでいない** ―― 完全に開通しており(普遍的充足)、開通した先に
高さの内容が無いだけである。判定の非対称性は設計の選択ではなく、**両 route の退化の仕方の
非対称性**として定理化された:

* **同一視 route**: `hull_bound` は無条件に充足可能・引き出せる結論は恒真(情報ゼロ);
* **非同一視 route**: 充足可能性 ⟺ 結論そのもの(R5 退化定理);
* **混合 route**(同一視で `hull_bound` を導出しつつ非同一視の `q_vol` で結論を読む):
  矛盾(4)。

なお「`q_vol` でなく `theta_vol` を落とす」変種は、フロベニオイド内部で**証明済み**の
次数計算(`theta_vol_derivation`)の否認を要するため、論文に忠実な転写としては
成立しない(ピンはどちらも論文由来であり、SS 由来の追加仮定ではない)。
望月側に残る可能性の記述(Θ-包ピンの結論非同値な導出)は R7 の判定から不変である。
-/

namespace IUT.Multiradial

open IUT.Arithmetic

/-! ## 1. 無条件補題 -/

/-- **無条件補題**: `−arithFactor ≤ C_Θ` は全ての算術データで成立する。

証明の核は恒等式 `C_Θ = P·X − arithFactor + 1/l`(`P = (l+1)l/(2 log q) > 0`、
`X = (1+12·d_mod/l)·D + 10·(e*·l+η) ≥ 0`)―― `C_Θ` 公式の `−(1/6)(1−12/l²)·log q` 項が
プロセッション正規化 `P` と掛け合わさって正確に `−arithFactor + (l+1)/l` を生む。
ゆえに同一視版転写(`identified_forces` が引き出す結論がこの不等式)は
**高さの情報を一切含まない**。 -/
theorem neg_arithFactor_le_cTheta (A : ArithmeticData) :
    -A.arithFactor ≤ A.cThetaFormula := by
  have hl0 : (0 : ℝ) < (A.l : ℝ) := A.l_cast_pos
  have hlq : (0 : ℝ) < A.logq := A.logq_pos
  have hl' : ((A.l : ℝ)) ≠ 0 := ne_of_gt hl0
  have hlq' : A.logq ≠ 0 := ne_of_gt hlq
  -- 恒等式: C_Θ = P·X − arithFactor + 1/l
  have hkey : A.cThetaFormula
      = ((A.l : ℝ) + 1) * (A.l : ℝ) / (2 * A.logq)
          * ((1 + 12 * A.dmod / (A.l : ℝ)) * A.D + 10 * (A.estar * (A.l : ℝ) + A.eta))
        - A.arithFactor + 1 / (A.l : ℝ) := by
    unfold ArithmeticData.cThetaFormula ArithmeticData.arithFactor
    field_simp
    ring
  have hP : (0 : ℝ) < ((A.l : ℝ) + 1) * (A.l : ℝ) / (2 * A.logq) :=
    div_pos (mul_pos (by linarith) hl0) (by linarith)
  have hdm : (0 : ℝ) ≤ A.dmod := zero_le_one.trans A.hdmod
  have hco : (0 : ℝ) ≤ 1 + 12 * A.dmod / (A.l : ℝ) := by
    have h12 : (0 : ℝ) ≤ 12 * A.dmod / (A.l : ℝ) := div_nonneg (by linarith) hl0.le
    linarith
  have hterm2 : (0 : ℝ) ≤ A.estar * (A.l : ℝ) + A.eta := by
    have h1 : (0 : ℝ) ≤ A.estar * (A.l : ℝ) :=
      mul_nonneg (zero_le_one.trans A.hestar) hl0.le
    linarith [A.heta]
  have hX : (0 : ℝ)
      ≤ (1 + 12 * A.dmod / (A.l : ℝ)) * A.D + 10 * (A.estar * (A.l : ℝ) + A.eta) := by
    have h1 := mul_nonneg hco A.hD
    linarith
  have hPX : (0 : ℝ) ≤ ((A.l : ℝ) + 1) * (A.l : ℝ) / (2 * A.logq)
      * ((1 + 12 * A.dmod / (A.l : ℝ)) * A.D + 10 * (A.estar * (A.l : ℝ) + A.eta)) :=
    mul_nonneg hP.le hX
  have h1l : (0 : ℝ) < 1 / (A.l : ℝ) := div_pos one_pos hl0
  rw [hkey]
  linarith

/-! ## 2. 同一視版転写 -/

/-- **同一視版転写**: `Thm311Transcription` の受信側ピン `q_vol` を、**同一視の法則**
`ident`(`volR ∘ kummer₀ = volS` ―― `TwoSidedLink.IsRelabeling` の log-Kummer 基底版、
「受信側正規化は送信側正規化の transport」= SS の言う「ℝ のコピーの同一視」の読み)で
**置換**したもの。他のフィールド(送信側ピン `theta_vol` = フロベニオイド内で証明済みの
Gaussian 次数計算、(Ind3) 包支配 `hull_dominates`、残余義務 `hull_bound`)は同一。

これが「同一視版の hull_bound の証明」の正確な形式化である ―― 通るか否かは
`identifiedTranscription_universal` が答える(通る、無条件に)。 -/
structure IdentifiedTranscription (A : ArithmeticData) where
  /-- log-Kummer 対応((Ind3) 上半両立性・増大鎖は証明済みの機構)。 -/
  K : IUT.LogTheta.LogKummerCorrespondence.{0, 0}
  /-- 受信側の体積。 -/
  volR : K.D → ℝ
  volR_mono : Monotone volR
  /-- 送信側の体積。 -/
  volS : K.F 0 → ℝ
  volS_mono : Monotone volS
  kummer0_mono : Monotone (K.kummer 0)
  /-- Θ標対象。 -/
  thetaPilot : K.F 0
  /-- **送信側ピン**(論文由来、`theta_vol_derivation` でフロベニオイド内部で導出済み)。 -/
  theta_vol : volS thetaPilot = A.arithFactor * (-A.qVol)
  /-- 受信側の包。 -/
  hullR : K.D
  /-- 包は全レベルの log-Kummer 像を支配((Ind3))。 -/
  hull_dominates : K.HullDominates thetaPilot hullR
  /-- ★ **同一視の法則**(`q_vol` ピンの代替): 受信側体積は基底 Kummer 写像に沿って
  送信側体積と一致する ―― `IsRelabeling` の転写レベル版。 -/
  ident : ∀ x : K.F 0, volR (K.kummer 0 x) = volS x
  /-- `hull_bound`(非同一視版と同一の義務)。 -/
  hull_bound : volR hullR ≤ A.cThetaFormula * A.qVol

/-- **同一視版転写の witness**(平行移動リンクの ℝ-モデル、`transcriptionOfCTheta` と
同型の構成 ―― ただし基底 Kummer 写像の値を送信側の値 `arithFactor·(−qVol)` に置く =
同一視の法則を機械的に満たす)。`hull_bound` は無条件補題から従う ――
**cΘ 閾値の仮定は不要**(非同一視版 witness との決定的差異)。 -/
noncomputable def identifiedTranscriptionOf (A : ArithmeticData) :
    IdentifiedTranscription A :=
  { K :=
      { D := ℝ
        F := fun _ => ℝ
        log := fun _ => id
        kummer := fun _ _ => A.arithFactor * (-A.qVol)
        upperSemi := fun _ _ => le_refl _ }
    volR := id
    volR_mono := monotone_id
    volS := fun _ => A.arithFactor * (-A.qVol)
    volS_mono := monotone_const
    kummer0_mono := monotone_const
    thetaPilot := 0
    theta_vol := rfl
    hullR := A.arithFactor * (-A.qVol)
    hull_dominates := fun _ => le_refl _
    ident := fun _ => rfl
    hull_bound := by
      have h := neg_arithFactor_le_cTheta A
      have hq := A.qVol_pos
      change A.arithFactor * (-A.qVol) ≤ A.cThetaFormula * A.qVol
      nlinarith }

/-- **同一視版は普遍的に通る**: 全ての算術データに対し同一視版転写が存在する ――
算術的入力ゼロ(非同一視版の `no_universal_transcription` と正反対)。
「同一視版の hull_bound の証明は通らないのか」への直接の答え: **通る、無条件に**。 -/
theorem identifiedTranscription_universal (A : ArithmeticData) :
    Nonempty (IdentifiedTranscription A) :=
  ⟨identifiedTranscriptionOf A⟩

/-! ## 3. 通った先に高さの情報は無い -/

/-- **同一視版が強制する結論**: containment(`hull_dominates` の基底レベル)+ 同一視の
法則 + `hull_bound` から引き出せるのは `−arithFactor ≤ C_Θ` ―― そしてこれは
`neg_arithFactor_le_cTheta` により**転写の存在を一切使わず証明済みの恒真命題**である。
非同一視版が強制する `−1 ≤ C_Θ`(= ε-窓で Szpiro 型高さ不等式)は**出ない**:
同一視は q標像の受信側体積を `−|log q|` から `arithFactor·(−|log q|)` へ押し下げ、
containment の下端がちょうど Gauss 利得のぶん深くなって高さの内容を吸収する。 -/
theorem identified_forces (A : ArithmeticData) (W : IdentifiedTranscription A) :
    -A.arithFactor ≤ A.cThetaFormula := by
  have h1 : W.volS W.thetaPilot ≤ W.volR W.hullR := by
    rw [← W.ident W.thetaPilot]
    exact W.volR_mono (W.K.base_le_hull W.hull_dominates)
  rw [W.theta_vol] at h1
  have h2 := W.hull_bound
  have hq := A.qVol_pos
  nlinarith

/-- **非同一視版は反例データで証明可能に失敗する**(対照の再確認):
`unconstrainedData`(`log q = 10⁶`, `D = 0`, `l = 7`)では `C_Θ < −1` ゆえ
`Thm311Transcription` は存在しない(R5 退化定理 + 判定テスト計算)。 -/
theorem honest_fails_unconstrained :
    ¬ Nonempty (Thm311Transcription unconstrainedData) :=
  fun ⟨W⟩ => exam_not_universally_passable (transcription_passes _ W)

/-- **同一視版は同じ反例データでも通る**: 非同一視版が不可能な地点
(`honest_fails_unconstrained`)でも同一視版転写は存在する ――
**同一視版の充足は高さ不等式の成否と無関係**であることの決定的実証
(同一視の道は開通しているが、高さについて何も語らない)。 -/
theorem identified_passes_unconstrained :
    Nonempty (IdentifiedTranscription unconstrainedData) :=
  identifiedTranscription_universal unconstrainedData

/-! ## 4. 「同一視で通らない」ものの正確な所在 -/

/-- **不能性の正確な所在**: 同一視の法則は `hull_bound` とではなく、**受信側ピン
`q_vol`**(q標像の受信側体積 = `−|log q|`)と衝突する ―― 非同一視版転写
`Thm311Transcription` に同一視の法則を追加すると矛盾する。

衝突する 2 つの値はどちらも論文内部の計算である(送信側 `arithFactor·(−qVol)` =
`theta_vol_derivation` のフロベニオイド内 Gaussian 次数、受信側 `−qVol` = Θリンクの
定義 + q の受信側次数)―― SS の外部仮定の衝突ではなく、**論文の 2 つの計算同士の衝突**。
`adjudication_not_relabeling` の転写レベル版であり、混合 route(同一視で `hull_bound` を
導出しつつ非同一視の `q_vol` で高さを読む)を閉じる。 -/
theorem identified_qvol_incompatible (A : ArithmeticData) (W : Thm311Transcription A)
    (hident : ∀ x : W.K.F 0, W.volR (W.K.kummer 0 x) = W.volS x) : False := by
  have h1 := hident W.thetaPilot
  rw [W.q_vol, W.theta_vol] at h1
  have hq := A.qVol_pos
  have hf := A.arithFactor_gt_one
  nlinarith [mul_pos (sub_pos.2 hf) hq]

/-! ## 5. Θ-包ピン(R7)の同一視版 -/

/-- **同一視版 Θ-包ピン付き転写**: `ThetaHullTranscription`(R7)の同一視版 ――
`IdentifiedTranscription` に多輻的表示の体積評価(Θ-包ピン)を追加。 -/
structure IdentifiedThetaHull (A : ArithmeticData) (L : ℝ)
    extends IdentifiedTranscription A where
  /-- 台帳は非負。 -/
  hL : 0 ≤ L
  /-- Θ-包ピン: 包の受信側体積 ≤ 送信側 Θ 体積 + 台帳。 -/
  theta_hull : volR hullR ≤ volS thetaPilot + L

/-- **同一視版は台帳 `L = 0` ですら Θ-包ピンを充足できる**(⟷ 非同一視版の
`no_lossless_theta_hull` は `L = 0` で充足不能)。同一視のもとでは包の受信側体積が
送信側の値そのものになるため、Θ-包ピンは等号で自明に成立する ―― SS の
「同一視すれば不等式は自明化する」の Θ-包ピンレベルでの正確な形式化。 -/
theorem identified_lossless_theta_hull (A : ArithmeticData) :
    Nonempty (IdentifiedThetaHull A 0) :=
  ⟨{ toIdentifiedTranscription := identifiedTranscriptionOf A
     hL := le_refl 0
     theta_hull := by
       change A.arithFactor * (-A.qVol) ≤ A.arithFactor * (-A.qVol) + 0
       simp }⟩

/-- **同一視版の高さ強制の消滅**: 非同一視版では Θ-包ピン + containment が高さ不等式
`(arithFactor−1)·qVol ≤ L` を強制した(`thetaHull_forces_height`)。同一視版で同じ
導出を実行すると得られるのは **`0 ≤ L`** のみ ―― Scholze–Stix の「0 ≤ 0 への崩壊」が、
台帳・Θ-包ピン込みの深さで正確に再現される。 -/
theorem identified_thetaHull_forces_only (A : ArithmeticData) {L : ℝ}
    (W : IdentifiedThetaHull A L) : 0 ≤ L := by
  have h1 : W.volS W.thetaPilot ≤ W.volR W.hullR := by
    rw [← W.ident W.thetaPilot]
    exact W.volR_mono (W.K.base_le_hull W.hull_dominates)
  have h2 := W.theta_hull
  linarith

/-! ## 6. 監査総括 -/

/-- **R8 総括(同一視監査の判定)**: (i) 同一視版転写は普遍的に存在(hull_bound は
同一視で「通る」)、(ii) 非同一視版が不可能な反例データでも通る(高さ情報ゼロ)、
(iii) 同一視版 Θ-包ピンは台帳 0 でも充足可能(⟷ 非同一視版は充足不能)、
(iv) 同一視の法則と受信側ピン `q_vol` の同時成立は矛盾(不能性の所在は `q_vol`)。

**バイアス監査の結論**: 形式化は同一視の道を塞いでいない ―― 開通しており、その先に
高さの内容が無い。R5–R7 の判定の非対称性は設計でなく、両 route の退化の仕方の
非対称性(同一視 = 無条件充足・情報ゼロ / 非同一視 = 充足 ⟺ 結論)である。 -/
theorem identification_audit_verdict :
    (∀ A : ArithmeticData, Nonempty (IdentifiedTranscription A))
    ∧ Nonempty (IdentifiedTranscription unconstrainedData)
    ∧ ¬ Nonempty (Thm311Transcription unconstrainedData)
    ∧ (∀ A : ArithmeticData, Nonempty (IdentifiedThetaHull A 0))
    ∧ (∀ A : ArithmeticData, ¬ Nonempty (ThetaHullTranscription A 0)) :=
  ⟨identifiedTranscription_universal,
   identified_passes_unconstrained,
   honest_fails_unconstrained,
   identified_lossless_theta_hull,
   no_lossless_theta_hull⟩

end IUT.Multiradial

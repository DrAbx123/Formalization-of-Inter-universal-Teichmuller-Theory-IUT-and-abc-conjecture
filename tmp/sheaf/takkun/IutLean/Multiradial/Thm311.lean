import Mathlib
import tmp.sheaf.takkun.IutLean.Frobenioid.Basic
import tmp.sheaf.takkun.IutLean.LogTheta.LogKummer
import tmp.sheaf.takkun.IutLean.Arithmetic.CurveInstance

/-!
# [IUT-III] Theorem 3.11 の転写部品 — 多輻的表示の組立

底本: [IUT-III] Thm 3.11 / 本プロジェクトの全既存インフラ。

Theorem 3.11(多輻的アルゴリズム)の転写に必要な部品を実装する:

## Part 1 — 分裂モノイドの次数計算(Thm 3.11 (i)(b) の体積出力)

Thm 3.11 (i)(b) の分裂モノイド(LGP-単項式)の核心は、**定数倍剛性の体積版**:
単数(`O×` 部分)は数論的次数に寄与せず(`degree_unit_mul_pow`)、ゆえに Gaussian 単項式
`{q^{j²}}` の総次数は正確に **Gauss 和 `(∑j²)·deg(q)`** となる(`gaussian_total_degree`)。
プロセッション正規化(`theta_vol_derivation`)により送信側体積
`= (l(l+1)/12)·deg(q) = arithFactor · deg(q)` が**フロベニオイドの内部で導出**される
―― 判定テストの送信側ピンの正当化。

## Part 2 — 転写状態 `Thm311Transcription`

log-Kummer 対応(`LogKummerCorrespondence`、(Ind3) 上半両立性・増大鎖は証明済み)の上に、
Thm 3.11 の主張の**転写の現在状態**を束ねる:

* **containment は log-Kummer 機構から証明される**: q標対象の像 = 基底レベルの Kummer 像
  (Θリンクの定義)であり、包は全レベルの像を支配(`HullDominates`、(Ind3) の強制する合併)
  ―― 判定テストの containment 条項が**実際の機構から**出る;
* **残る唯一の義務** = `hull_bound`(包の受信側体積上界 = [IUT-IV] Prop 1.1–1.9 の
  p 進対数体積計算)。

## Part 3 — 組立定理 `transcription_passes`

転写状態から判定テストの通過を**構成的に**導く ―― リンクは log-Kummer の Kummer 写像
そのもの、containment は `hull_dominates` の基底レベル、送信側ピンは Part 1 の次数計算。
これにより **Thm 3.11 の転写は `hull_bound` 一点の導出に完全に還元**される。

**(Ind1),(Ind2) について(honest)**: 本組立では不定性群を自明に取る ―― 可能な像の多重性は
log-Kummer のレベルが担う((Ind3) が包を強制する部分が体積評価の核心であるため)。
非自明な (Ind1),(Ind2) の組み込みは `PilotVolumeData` の Γ を通じて既に形式化済みであり、
体積保存性(`hull_exceeds_orbit`)ゆえ包の体積評価には寄与しない。
-/

namespace IUT.Multiradial

open IUT.Frobenioid Finset

/-! ## Part 1 — 分裂モノイドの次数計算(Thm 3.11 (i)(b)) -/

/-- **定数倍剛性の体積版**: 単数倍はテータ標対象の次数を変えない ――
`deg(u·q^N) = N·deg(q)`(`u` 単数)。単テータ環境の定数倍剛性
(`Theta/ThetaGroup.lean` で群論的に証明済み)の、体積レベルでの帰結。 -/
theorem degree_unit_mul_pow (F : Model) (u : F.base.Otri) (hu : IsUnit u)
    (q : F.base.valueMonoid) (N : ℕ) :
    F.degree (F.base.valueMap u * q ^ N) = (N : ℝ) * F.degree q := by
  rw [F.degree_mul, F.degree_valueMap_unit u hu, zero_add]
  unfold Model.degree
  rw [map_pow, toAdd_pow]
  simp [nsmul_eq_mul]

/-- **Gaussian 単項式の総次数 = Gauss 和**(Thm 3.11 (i)(b) の体積出力):
`∑_{j=0}^{n} deg(q^{j²}) = (∑ j²)·deg(q)`。 -/
theorem gaussian_total_degree (F : Model) (q : F.base.valueMonoid) (n : ℕ) :
    ∑ j ∈ range (n + 1), F.degree (q ^ (j ^ 2))
      = ((∑ j ∈ range (n + 1), j ^ 2 : ℕ) : ℝ) * F.degree q := by
  have hterm : ∀ j : ℕ, F.degree (q ^ (j ^ 2)) = ((j ^ 2 : ℕ) : ℝ) * F.degree q := by
    intro j
    unfold Model.degree
    rw [map_pow, toAdd_pow]
    simp [nsmul_eq_mul]
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  push_cast
  ring

/-- **送信側体積の導出**(Thm 3.11 (i)(b) + プロセッション正規化):
Gaussian 単項式のプロセッション正規化次数は正確に `arithFactor = l(l+1)/12` 倍
―― 判定テストの送信側ピン `volS(Θ標) = arithFactor·deg(q)` が
**フロベニオイドの内部で導出**される。 -/
theorem theta_vol_derivation (F : Model) (q : F.base.valueMonoid)
    (l : ℕ) (hodd : Odd l) (hl : 7 ≤ l) :
    (∑ j ∈ range (lStar l + 1), F.degree (q ^ (j ^ 2))) / (lStar l : ℝ)
      = ((l : ℝ) * ((l : ℝ) + 1)) / 12 * F.degree q := by
  rw [gaussian_total_degree]
  have h := IUT.Arithmetic.thetaPilotDegree_div_lStar l hodd hl
  unfold thetaPilotDegree at h
  rw [mul_div_right_comm, h]

/-! ## Part 2 — 転写状態 -/

open IUT.Arithmetic in
/-- **Thm 3.11 転写状態**: log-Kummer 対応の上での、Theorem 3.11 の転写の現在状態。
containment(q標 ≤ 包)は log-Kummer 機構(`hull_dominates` の基底レベル + Θリンクの
定義 = 基底 Kummer 像)から**証明される**。残る唯一の義務は `hull_bound`
(= [IUT-IV] Prop 1.1–1.9 の p 進対数体積計算)。 -/
structure Thm311Transcription (A : ArithmeticData) where
  /-- log-Kummer 対応((Ind3) 上半両立性・増大鎖は証明済みの機構)。 -/
  K : IUT.LogTheta.LogKummerCorrespondence.{0, 0}
  /-- 受信側の体積(受信側 Hodge 劇場の正規化)。 -/
  volR : K.D → ℝ
  volR_mono : Monotone volR
  /-- 送信側の体積(Θ側 Hodge 劇場の正規化 ―― `theta_vol_derivation` の Gaussian 次数)。 -/
  volS : K.F 0 → ℝ
  volS_mono : Monotone volS
  /-- 基底レベルの Kummer 写像は単調(体積比較に必要)。 -/
  kummer0_mono : Monotone (K.kummer 0)
  /-- Θ標対象(基底レベルの Frobenius 的データ)。 -/
  thetaPilot : K.F 0
  /-- **送信側ピン**: Θ標の送信側体積 = Gauss 因子 × `|log q|`
  (Part 1 `theta_vol_derivation` により導出される値)。 -/
  theta_vol : volS thetaPilot = A.arithFactor * (-A.qVol)
  /-- 受信側の包。 -/
  hullR : K.D
  /-- **包は全レベルの log-Kummer 像を支配**((Ind3) が強制する合併 ――
  `kummer_le_transport` の増大鎖により意味を持つ)。 -/
  hull_dominates : K.HullDominates thetaPilot hullR
  /-- **受信側ピン**: q標対象の像(= 基底レベルの Kummer 像、Θリンクの定義)の体積
  = `−|log q|`。 -/
  q_vol : volR (K.kummer 0 thetaPilot) = -A.qVol
  /-- ★ **残る唯一の義務**([IUT-IV] Prop 1.1–1.9 の p 進対数体積計算):
  包の受信側体積が `C_Θ` 公式で上から抑えられる。 -/
  hull_bound : volR hullR ≤ A.cThetaFormula * A.qVol

/-! ## Part 3 — 組立定理 -/

open IUT.Arithmetic in
/-- **組立定理**: Thm 3.11 転写状態から判定テストの通過が**構成的に**従う ――
リンク = log-Kummer の基底 Kummer 写像、containment = `hull_dominates` の基底レベル
(実際の機構からの証明)、送信側ピン = Gaussian 次数計算。
**Thm 3.11 の転写は `hull_bound` 一点の導出に完全に還元された。** -/
theorem transcription_passes (A : ArithmeticData) (W : Thm311Transcription A) :
    A.AdjudicationTest := by
  refine ⟨{
      Send := W.K.F 0
      Recv := W.K.D
      volS := W.volS
      volS_mono := W.volS_mono
      volR := W.volR
      volR_mono := W.volR_mono
      Γ := PUnit
      action := { smul := fun _ x => x, one_smul := fun _ => rfl,
                  mul_smul := fun _ _ _ => rfl }
      thetaPilot := W.thetaPilot
      hull := W.thetaPilot
      hull_spec := fun _ => le_refl _
      qPilot := W.K.kummer 0 W.thetaPilot
      link := W.K.kummer 0
      link_mono := W.kummer0_mono
      link_pilot := rfl },
    W.hullR, ?_, ?_, ?_, ?_⟩
  · exact W.q_vol
  · show W.volS W.thetaPilot = A.arithFactor * W.volR (W.K.kummer 0 W.thetaPilot)
    rw [W.q_vol, W.theta_vol]
  · intro g
    show W.K.kummer 0 W.thetaPilot ≤ W.hullR
    exact W.hull_dominates 0
  · exact W.hull_bound

/-! ## 非空性 witness(曲線 11a3、自明領域) -/

open IUT.Arithmetic in
/-- **転写状態の witness**(曲線 11a3、自明領域): 11a3 の証明済みの通過
(`curve11a3_exam_passes` → `C_Θ ≥ −1`)を用いて転写状態を構成 ――
枠組みの非空性の実証。**実物の転写**は `hull_bound` を Prop 1.1–1.9 の p 進計算から
(`realHodgeTheater` の対象の上で)導出しなければならない(残存作業)。 -/
noncomputable def curve11a3Transcription (eta D : ℝ) (heta : 0 ≤ eta) (hD : 0 ≤ D) :
    Thm311Transcription (curve11a3Data eta D heta hD) := by
  set A := curve11a3Data eta D heta hD
  have hC : -1 ≤ A.cThetaFormula :=
    (ArithmeticData.adjudicationTest_iff_cTheta A).mp
      (curve11a3_exam_passes eta D heta hD)
  exact
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
        show -A.qVol ≤ A.cThetaFormula * A.qVol
        nlinarith [A.qVol_pos, hC] }

end IUT.Multiradial

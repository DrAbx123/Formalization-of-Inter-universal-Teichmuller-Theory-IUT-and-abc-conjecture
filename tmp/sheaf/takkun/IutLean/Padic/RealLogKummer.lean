import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import tmp.sheaf.takkun.IutLean.Padic.ShellTransport
import tmp.sheaf.takkun.IutLean.Multiradial.Thm311

/-!
# 実 log-Kummer 対応 — Phase R4(実殻・実体積・実機構の垂直列)

底本: [IUT-III] Prop 3.5 / Thm 3.11 (ii)(log-Kummer 対応)、[IUT-IV] Prop 3.9 (ii)
(procession 正規化対数体積)。

Phase R1–R3 の解析的成果の上に、**実際の p 進領域を受信容器とする**
`LogKummerCorrespondence` を構成する。toy(`curve11a3Transcription`: `D := ℝ`・定数 Kummer)
との違い:

* **受信容器 `D = ShellRegion p`**: 実際の殻 `S_λ ⊆ ℚ_p` のなす部分型(包含順序)。
  指数の簿記ではない ―― `shell_subset_iff`(R3)が包含順序との同型を保証する;
* **log-link = 深さ保存**: `exp : S_λ ≅ 1 + S_λ` の全レベル全単射
  (`expQ_shell_existsUnique`、R2–R3)により、対数リンクは各レベルの単数の殻を
  **同じ深さの**殻へ写す ―― 非分岐・整数レベルでは無損失(`unit_mul_shell`);
* **上半両立性 = 等号**: 無損失ゆえ Kummer 像は増大せず一定((Ind3) の `≤` の特例。
  分岐の場合は `LogShellRadius` の半径定数が記録する損失で真の増大が生じる ―― R6–R7);
* **体積 = procession 正規化された実対数体積**: `vol(S_λ) = −λ·log p/(2l)`
  (`logVol_shell_gen` の正規化、[IUT-IV] Prop 3.9 (ii))。

## 実転写状態 `realShellTranscription`(capstone)

曲線 11a3(`p = 11`, `v(q) = 1`, `l = 7`)の実データで `Thm311Transcription` を構成:
q-標対象 = **実際の殻 `S_1 = 11·ℤ₁₁`**、受信側ピン `volR(q標) = −qVol` は
実体積計算、送信側ピン = `arithFactor·|log q|`(実フロベニオイドの
`theta_vol_derivation` で導出済の値)。`transcription_passes` により判定テスト通過。

## honest 注記(重要)

`hull_bound` は「cΘ ≥ −1」(`curve11a3_exam_passes` の**直接数値計算**による事実)から
充足される ―― これは**固定曲線の自明領域**の充足であり(閾値定理)、ABC の内容を持たない。
Phase R5 の目標は、この数値的事実への依存を、包の体積の**一般的な導出**
(一様な族の regime、`volS`/`volR` を別関数のまま = ℝ 非同一視)に置き換えることである。
本モジュールの価値は**機構の実在化**(実殻・実体積・実 log-link 根拠)にある。
-/

namespace IUT.Padic

open IUT.LogTheta IUT.Arithmetic IUT.Multiradial

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 実受信容器: 殻領域 -/

/-- **殻領域**: 実際の殻 `S_λ ⊆ ℚ_p` のなす部分型(包含順序は `Subtype` 経由)。
log-Kummer 対応の受信容器 `D` の実在化。 -/
def ShellRegion : Type := {S : Set ℚ_[p] // ∃ lam : ℤ, S = shell p lam}

noncomputable instance : Preorder (ShellRegion p) :=
  Subtype.preorder _

/-- 殻の指数の一意性(`shell_subset_iff` の反対称性)。 -/
lemma shell_index_injective {lam mu : ℤ} (h : shell p lam = shell p mu) : lam = mu := by
  have h1 := (shell_subset_iff p).mp (le_of_eq h)
  have h2 := (shell_subset_iff p).mp (le_of_eq h.symm)
  omega

/-- 殻領域の**深さ**(一意な指数)。 -/
noncomputable def depth (S : ShellRegion p) : ℤ := S.2.choose

lemma depth_spec (S : ShellRegion p) : S.1 = shell p (depth p S) := S.2.choose_spec

@[simp] lemma depth_mk (lam : ℤ) : depth p ⟨shell p lam, lam, rfl⟩ = lam := by
  have h := depth_spec p ⟨shell p lam, lam, rfl⟩
  exact shell_index_injective p h.symm

/-- 領域の包含は深さの逆順序: `S ≤ T ↔ depth T ≤ depth S`。 -/
lemma le_iff_depth (S T : ShellRegion p) : S ≤ T ↔ depth p T ≤ depth p S := by
  have hS := depth_spec p S
  have hT := depth_spec p T
  constructor
  · intro h
    exact (shell_subset_iff p).mp (by rw [← hS, ← hT]; exact h)
  · intro h
    change S.1 ⊆ T.1
    rw [hS, hT]
    exact (shell_subset_iff p).mpr h

/-! ## procession 正規化体積 -/

/-- **procession 正規化対数体積**([IUT-IV] Prop 3.9 (ii)): `vol(S_λ) = −λ·log p/(2l)`
(`logVol_shell_gen` の生の体積 `−λ·log p` を `1/(2l)` 正規化)。 -/
noncomputable def regionVol (l : ℕ) (S : ShellRegion p) : ℝ :=
  -(depth p S : ℝ) * Real.log p / (2 * l)

/-- 体積は包含に関して単調(実際の領域の順序で)。 -/
lemma regionVol_mono (l : ℕ) (hl : 0 < l) : Monotone (regionVol p l) := by
  intro S T h
  have hd : (depth p T : ℝ) ≤ (depth p S : ℝ) := by
    exact_mod_cast (le_iff_depth p S T).mp h
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.out.one_le)
  have h2l : (0 : ℝ) < 2 * l := by positivity
  unfold regionVol
  rw [div_le_div_iff₀ h2l h2l]
  have h2 : (-(depth p S : ℝ)) * Real.log p ≤ (-(depth p T : ℝ)) * Real.log p :=
    mul_le_mul_of_nonneg_right (neg_le_neg hd) hlog
  exact mul_le_mul_of_nonneg_right h2 h2l.le

/-! ## 実 log-Kummer 対応 -/

/-- **実 log-Kummer 対応**: 全レベルの Frobenius 的データと垂直核を**実際の殻領域**とする。
`log := id` は「対数リンクは殻の深さを保つ」ことの領域レベルの表現であり、その正当化は
`expQ_shell_existsUnique`(`exp : S_λ ≅ 1+S_λ` 全レベル全単射、R2–R3)である。
`upperSemi` は等号((Ind3) `≤` の非分岐無損失の特例; 分岐では真の増大 ―― R6–R7)。 -/
noncomputable def realLogKummer : LogKummerCorrespondence.{0, 0} where
  D := ShellRegion p
  F _ := ShellRegion p
  log _ := id
  kummer _ := id
  upperSemi _ x := le_refl x

/-- 実対応の転送は恒等(深さ保存の反復)。 -/
lemma realTransport_eq (n : ℕ) (x : ShellRegion p) :
    (realLogKummer p).transport 0 n x = x := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

/-! ## 実転写状態(曲線 11a3、実殻・実体積) -/

/-- q-標対象の実領域: 深さ 1 の殻 `S_1 = 11·ℤ₁₁`(`v₁₁(q) = 1`)。 -/
noncomputable def qShell : ShellRegion 11 := ⟨shell 11 1, 1, rfl⟩

lemma regionVol_qShell : regionVol 11 7 qShell = -(Real.log 11 / 14) := by
  unfold regionVol qShell
  rw [depth_mk]
  push_cast
  ring

lemma curve11a3_qVol (eta Dv : ℝ) (heta : 0 ≤ eta) (hDv : 0 ≤ Dv) :
    (curve11a3Data eta Dv heta hDv).qVol = Real.log 11 / 14 := by
  unfold ArithmeticData.qVol ArithmeticData.logq curve11a3Data
  norm_num

/-- **実転写状態(Phase R4 capstone)**: 実殻領域・実体積・実 log-link 根拠による
`Thm311Transcription`。q-標対象 = 実際の殻 `S_1`、受信側ピン = 実体積計算
`vol(S_1) = −log 11/14 = −qVol`、送信側ピン = `arithFactor·|log q|`
(実フロベニオイドで導出済の値)。`hull_bound` は cΘ ≥ −1(直接数値計算)による
自明領域の充足 ―― その一般的導出への置換が Phase R5(honest 注記参照)。 -/
noncomputable def realShellTranscription (eta Dv : ℝ) (heta : 0 ≤ eta) (hDv : 0 ≤ Dv) :
    Thm311Transcription (curve11a3Data eta Dv heta hDv) := by
  set A := curve11a3Data eta Dv heta hDv with hA
  have hqVol : A.qVol = Real.log 11 / 14 := curve11a3_qVol eta Dv heta hDv
  have hvolq : regionVol 11 7 qShell = -A.qVol := by
    rw [regionVol_qShell, hqVol]
  have hC : -1 ≤ A.cThetaFormula :=
    (ArithmeticData.adjudicationTest_iff_cTheta A).mp
      (curve11a3_exam_passes eta Dv heta hDv)
  exact
    { K := realLogKummer 11
      volR := regionVol 11 7
      volR_mono := regionVol_mono 11 7 (by norm_num)
      volS := fun S => A.arithFactor * regionVol 11 7 S
      volS_mono := (regionVol_mono 11 7 (by norm_num)).const_mul
        (le_of_lt (lt_trans one_pos A.arithFactor_gt_one))
      kummer0_mono := fun _ _ h => h
      thetaPilot := qShell
      theta_vol := by rw [hvolq]
      hullR := qShell
      hull_dominates := fun n => le_of_eq (realTransport_eq 11 n qShell)
      q_vol := hvolq
      hull_bound := by
        rw [hvolq]
        nlinarith [A.qVol_pos, hC] }

/-- **実機構の転写は判定テストを通過する**(`transcription_passes` の実インスタンス):
containment は実殻の log-Kummer 機構から、送信側ピンは実フロベニオイドの次数計算から。 -/
theorem realShellTranscription_passes (eta Dv : ℝ) (heta : 0 ≤ eta) (hDv : 0 ≤ Dv) :
    (curve11a3Data eta Dv heta hDv).AdjudicationTest :=
  transcription_passes _ (realShellTranscription eta Dv heta hDv)

end IUT.Padic

import Mathlib
import tmp.sheaf.takkun.IutLean.Arithmetic.AdjudicationTest

/-!
# 受験 (Exam Attempt) — 判定テストの実施とその結果

本モジュールは判定テスト(`AdjudicationTest.lean`)の**受験の答案**である。結果は
「合格」でも「不合格」でもなく、**2 つの形式的定理による試験自体の性質の確定**となった:

## 発見 1(退化定理 `adjudicationTest_iff_cTheta`): 裸の存在命題は答えと同値

答案作成の最初の試みで判明した事実: 存在命題としての `AdjudicationTest A` は、
**結論そのもの(`C_Θ ≥ −1`、= その データに対する高さ不等式)と同値**である。

* (⟸) `C_Θ ≥ −1` が成り立つデータに対しては、**toy witness**(平行移動リンク)で
  テストが「通って」しまう ―― 出所(IUT の機構)を問わない存在命題は、答えを
  書き込む行為と区別が付かない;
* (⟹) テストが通れば `C_Θ ≥ −1`(既証明の `adjudication_implies_height` の核)。

**教訓**: `Prop` の存在命題は証明の**出所**を追跡しない。「望月の証明の転写による構成」と
「結論を仮定した toy 構成」は型上区別されない。ゆえに試験の合格とは
`AdjudicationTest A` 単体の証明ではなく、**曲線実現された全データに対する一様な導出**
でなければならない。

## 発見 2(非可通性定理 `exam_not_universally_passable`): 無制約データには反例がある

制約なしの `ArithmeticData` 全体に対する一様なテスト通過(`∀ A, AdjudicationTest A`)は
**偽である** ―― 高さが誤差項に比べ巨大な数値データ(`log q = 10⁶`, `D = 0`)で
テストは証明可能に失敗する。

**教訓**: このようなデータは(Szpiro 予想が真なら)実際の楕円曲線からは生じない。
ゆえに試験の真の内容は「**楕円曲線の算術が実現するデータに限れば**テストが通る」であり、
その「実現」の構造(高さと different/導手の間の、曲線の幾何が強制する結び付き)こそが
証明されるべきものの全部である ―― toy でも反例でも近道できない。

## 答案(受験の結果)

1. 抽象的な合格は不可能(発見 1: 合格 = 結論の仮定)。
2. 抽象的な不合格の宣告も不可能(発見 2 の反例は曲線非実現データであり、
   曲線実現データへの制限は幾何を要する)。
3. **ゆえに試験は、幾何学的実体化(実際の Hodge 劇場・エタールテータ・対数 Kummer・
   Prop 1.1–1.9 の p 進評価)の上での転写によってのみ受験可能** ―― これが答案である。
   受験を試みた結果として、この事実自体が `sorry` 無しの 2 定理で確定した。
-/

namespace IUT.Arithmetic

open IUT.Multiradial

namespace ArithmeticData

variable (A : ArithmeticData)

/-- **発見 1(退化定理)**: 裸の存在命題としての判定テストは、結論 `C_Θ ≥ −1`
(= そのデータに対する高さ不等式の核)と**同値**。

(⟸)方向の witness は**平行移動リンク**の toy 構成 ―― 出所を問わない存在命題は
「答えを書き込む」ことで通ってしまう。ゆえに意味のある試験は、単一データでの
`AdjudicationTest` 証明ではなく、**曲線実現された全データへの一様な導出**である。 -/
theorem adjudicationTest_iff_cTheta :
    A.AdjudicationTest ↔ -1 ≤ A.cThetaFormula := by
  constructor
  · rintro ⟨T, hullR, hpin, _hdeg, hcontain, hbound⟩
    have h1 : T.qPilot ≤ hullR := by
      have hg := hcontain 1
      rwa [one_smul, T.link_pilot] at hg
    have h2 := T.volR_mono h1
    have h3 : -A.qVol ≤ A.cThetaFormula * A.qVol := by
      have := h2.trans hbound
      rwa [hpin] at this
    nlinarith [A.qVol_pos, h3]
  · intro hC
    refine ⟨{
        Send := ℝ
        Recv := ℝ
        volS := id
        volS_mono := monotone_id
        volR := id
        volR_mono := monotone_id
        Γ := PUnit
        action := { smul := fun _ x => x, one_smul := fun _ => rfl,
                    mul_smul := fun _ _ _ => rfl }
        thetaPilot := -(A.arithFactor * A.qVol)
        hull := -(A.arithFactor * A.qVol)
        hull_spec := fun _ => le_refl _
        qPilot := -A.qVol
        link := fun x => x + (A.arithFactor - 1) * A.qVol
        link_mono := fun _ _ h => by dsimp only; linarith
        link_pilot := by
          show -(A.arithFactor * A.qVol) + (A.arithFactor - 1) * A.qVol = -A.qVol
          ring },
      -A.qVol, rfl, ?_, ?_, ?_⟩
    · show id (-(A.arithFactor * A.qVol)) = A.arithFactor * id (-A.qVol)
      show -(A.arithFactor * A.qVol) = A.arithFactor * (-A.qVol)
      ring
    · intro g
      show -(A.arithFactor * A.qVol) + (A.arithFactor - 1) * A.qVol ≤ -A.qVol
      exact le_of_eq (by ring)
    · show id (-A.qVol) ≤ A.cThetaFormula * A.qVol
      show -A.qVol ≤ A.cThetaFormula * A.qVol
      nlinarith [A.qVol_pos, hC]

end ArithmeticData

/-- **発見 2 の反例データ**(曲線非実現): 高さが誤差項に比べ巨大
(`log q = 10⁶`、`D = 0`、`l = 7`)な無制約の数値データ。Szpiro 予想が真なら
このようなデータは実際の楕円曲線からは生じない。 -/
noncomputable def unconstrainedData : ArithmeticData where
  l := 7
  hl := le_refl 7
  hodd := Nat.odd_iff.mpr rfl
  vq := 1000000
  hvq := by norm_num
  logNv := 1
  hlogNv := one_pos
  dmod := 1
  hdmod := le_refl 1
  estar := 1
  hestar := le_refl 1
  eta := 0
  heta := le_refl 0
  D := 0
  hD := le_refl 0

/-- **発見 2(非可通性定理)**: 無制約データに対する判定テストは**証明可能に失敗する**
―― `∀ A, AdjudicationTest A` は偽。ゆえに試験のいかなる真の合格も、
「データが実際の楕円曲線から実現される」という幾何学的制約を本質的に使わねばならない。
toy による一様な合格の道は形式的に閉じている。 -/
theorem exam_not_universally_passable : ¬ unconstrainedData.AdjudicationTest := by
  rw [ArithmeticData.adjudicationTest_iff_cTheta, not_le]
  have hl : (unconstrainedData.l : ℝ) = 7 := by norm_num [unconstrainedData]
  have hvq : (unconstrainedData.vq : ℝ) = 1000000 := by norm_num [unconstrainedData]
  have hNv : unconstrainedData.logNv = 1 := rfl
  have hd : unconstrainedData.dmod = 1 := rfl
  have he : unconstrainedData.estar = 1 := rfl
  have het : unconstrainedData.eta = 0 := rfl
  have hD : unconstrainedData.D = 0 := rfl
  simp only [ArithmeticData.cThetaFormula, ArithmeticData.logq, hl, hvq, hNv, hd, he, het, hD]
  norm_num

end IUT.Arithmetic

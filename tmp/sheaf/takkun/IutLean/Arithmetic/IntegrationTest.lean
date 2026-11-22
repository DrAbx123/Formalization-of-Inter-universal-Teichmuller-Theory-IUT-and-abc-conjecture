import Mathlib
import tmp.sheaf.takkun.IutLean.Arithmetic.CurveInstance
import tmp.sheaf.takkun.IutLean.Arithmetic.RealHodgeTheater
import tmp.sheaf.takkun.IutLean.Padic.LogVolume
import tmp.sheaf.takkun.IutLean.LogTheta.LogShell

/-!
# 統合判定テスト — 実楕円曲線から Hodge 劇場・対数殻・p 進正規化体積・Θ リンクまで

**目的**: 実在の楕円曲線 11a3(`y² + y = x³ − x²`)から出発し、IUT の主要装置
(Hodge 劇場・対数殻・p 進正規化体積・Θ リンク)を**実際のデータで**構成して
型が通ることを判定する統合テスト。このモジュールが `lake build` で緑になること自体が
テストの合格である。

## テストの鎖(何が実で何が引用か)

1. **実曲線**: `curve11a3 : WeierstrassCurve ℚ`、`Δ = −11`・`c₄ = 16`(計算済)。
   本モジュールで新たに `IsElliptic` インスタンスと **j-不変量 `j = −4096/11`** を計算。
2. **11 進局所不変量(新実装)**: `‖Δ‖₁₁ = 11⁻¹`(`v₁₁(Δ) = 1`)、`‖c₄‖₁₁ = 1`
   (11 進単数)、`‖j‖₁₁ = 11`(j の 11 での極 = Tate 曲線)―― **Tate の乗法的還元
   判定が実際の `ℚ_[11]` のノルムとして計算される**。`v(q) = v(Δ) = 1` の同定
   (Tate の q-展開理論)のみ引用。
3. **p 進正規化体積**: `logVol(Δ·ℤ₁₁) = −log 11`(判別式の殻 = q の殻の体積、
   `Padic/LogVolume.lean` の `μ_log` 正規化)。
4. **対数殻(新実装)**: `realLogShell`(台 = `ℤ_[11]` = 正則整構造を含むコンパクト
   加法群)+ `realLogLink`(**値群成分**: `u ↦ v₁₁(u)` は真の加法準同型
   `Additive ℚ_[11]ˣ →+ ℤ_[11]`)。単数部の解析的対数(`logOnePlus`、ノルム保存 =
   体積保存)は `realLogShell_analytic` として搭載 ―― その加法性(準同型性)のみが
   既知の残余。
5. **Θ リンク(新実装)**: `realFStrip`(実 F-プライム縞: `Π_v = G_v =` 実際の
   `Gal(ℚ̄_p/ℚ_p)`、`O▷` 側 `Mon = ℚ̄_pˣ`、実 Galois 作用)の上の
   `realThetaLink : ThetaLink realFStrip realFStrip`(モノ解析的核 `D⊢` の同一視;
   恒等代表 ―― 実物の full poly-isomorphism の軌道の代表点)。
6. **Hodge 劇場**: `realHodgeTheater`(`l = 7`、`7 ∤ Δ = −11` ✓)。

**総合 witness**: `integrationWitness : IntegrationWitness` が全部品を単一のレコードに
束ね、`integration_test_passes` が数値的事実を束ねる。

## 残余(honest)

* `v(q) = v(Δ)` の形式的導出(Tate の q-展開理論、Mathlib 未整備);
* 対数リンクの単数部の加法性(p 進 log の準同型性);
* Θ リンクの「実物」は full poly-isomorphism(全同型の軌道)であり、ここでの恒等代表は
  その一点(非自明な代表・(Ind1)(Ind2) 軌道は `LogTheta/Indeterminacy.lean` で形式化済)。
-/

namespace IUT.Arithmetic

open IUT.Frobenioid IUT.LogTheta

/-! ## 1. 実曲線の楕円性と j-不変量 -/

instance : curve11a3.IsElliptic :=
  ⟨by rw [curve11a3_Δ]; exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

/-- **j-不変量の計算**: `j(11a3) = −4096/11` ―― 分母に 11 が現れる
(`v₁₁(j) = −1` ⟹ 11 で potentially multiplicative)。 -/
theorem curve11a3_j : curve11a3.j = -4096 / 11 := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    curve11a3_Δ, curve11a3_c₄]
  norm_num

/-! ## 2. 11 進局所不変量(Tate 判定の実計算) -/

/-- `‖Δ‖₁₁ = 11⁻¹`: 判別式の 11 進ノルム(`v₁₁(Δ) = 1` のノルム読み)。 -/
theorem curve11a3_Δ_norm : ‖(curve11a3.Δ : ℚ_[11])‖ = (11 : ℝ)⁻¹ := by
  have hcast : (curve11a3.Δ : ℚ_[11]) = -(((11 : ℕ)) : ℚ_[11]) := by
    rw [curve11a3_Δ]; push_cast; ring
  rw [hcast, norm_neg, Padic.norm_p]
  norm_num

/-- `‖c₄‖₁₁ = 1`: `c₄ = 16` は 11 進単数。 -/
theorem curve11a3_c₄_norm : ‖(curve11a3.c₄ : ℚ_[11])‖ = 1 := by
  have hcast : (curve11a3.c₄ : ℚ_[11]) = ((16 : ℕ) : ℚ_[11]) := by
    rw [curve11a3_c₄]; push_cast; ring
  rw [hcast]
  exact Padic.norm_natCast_eq_one_iff.mpr (by decide)

/-- `‖j‖₁₁ = 11`: j-不変量は 11 で 1 位の極を持つ(`|j| > 1` = Tate 曲線の領域)。 -/
theorem curve11a3_j_norm : ‖(curve11a3.j : ℚ_[11])‖ = 11 := by
  have hcast : (curve11a3.j : ℚ_[11])
      = -(((4096 : ℕ)) : ℚ_[11]) / (((11 : ℕ)) : ℚ_[11]) := by
    rw [curve11a3_j]; push_cast; ring
  rw [hcast, norm_div, norm_neg, Padic.norm_p,
    Padic.norm_natCast_eq_one_iff.mpr (by decide)]
  norm_num

/-- **Tate の乗法的還元判定(実計算)**: `v₁₁(Δ) = 1 > 0` かつ `c₄` が 11 進単数
―― 11a3 は 11 で乗法的還元(node)であり、Tate parameter は `v₁₁(q) = v₁₁(Δ) = 1`、
q の殻 = `11·ℤ₁₁`(`v(q) = v(Δ)` の同定のみ Tate 理論の引用)。 -/
theorem curve11a3_tate_criterion :
    ‖(curve11a3.Δ : ℚ_[11])‖ < 1 ∧ ‖(curve11a3.c₄ : ℚ_[11])‖ = 1 :=
  ⟨by rw [curve11a3_Δ_norm]; norm_num, curve11a3_c₄_norm⟩

/-! ## 3. p 進正規化体積(判別式の殻 = q の殻) -/

/-- **q の殻の正規化対数体積(実計算)**: `μ_log(Δ·ℤ₁₁) = −log 11`。
`v(q) = v(Δ) = 1` により、これは Tate parameter の殻 `q·ℤ₁₁ = 11·ℤ₁₁` の体積であり、
判定テストの `−logq`(`ArithmeticData.logq`)・受信側ピン `−qVol` の生の実現
(`Padic/LogVolume.lean` の `curve11a3_qShell_logVol` と整合)。 -/
theorem curve11a3_Δ_logVol :
    IUT.Padic.logVol (curve11a3.Δ : ℚ_[11]) = -Real.log 11 := by
  unfold IUT.Padic.logVol
  rw [curve11a3_Δ_norm, Real.log_inv]

/-! ## 4. 実対数殻と実対数リンク -/

/-- **実対数殻**: 台 = `ℤ_[11]`(正則的整構造 `(O_Fv)+` を含むコンパクト加法群、
`I ⊗ ℚ = ℚ_[11]`)。[IUT-III] Def 1.1 の対数殻 (a) の実現。 -/
noncomputable def realLogShell : LogShell.{0} := { carrier := ℤ_[11] }

/-- **実対数写像(値群成分)**: `u ↦ v₁₁(u)`(11 進付値)は乗法を加法へ送る
**真の加法準同型** `Additive ℚ_[11]ˣ →+ ℤ_[11]`(`v(uv) = v(u) + v(v)`)。 -/
noncomputable def realLogMap : Additive ℚ_[11]ˣ →+ ℤ_[11] where
  toFun u := ((((Additive.toMul u : ℚ_[11]ˣ) : ℚ_[11]).valuation : ℤ) : ℤ_[11])
  map_zero' := by
    change (((((1 : ℚ_[11]ˣ) : ℚ_[11])).valuation : ℤ) : ℤ_[11]) = 0
    rw [Units.val_one, Padic.valuation_one, Int.cast_zero]
  map_add' u v := by
    change ((((Additive.toMul u * Additive.toMul v : ℚ_[11]ˣ) : ℚ_[11]).valuation : ℤ)
        : ℤ_[11]) = _
    rw [Units.val_mul, Padic.valuation_mul (Units.ne_zero _) (Units.ne_zero _),
      Int.cast_add]

/-- **実対数リンク(値群成分)**: 実対数写像を対数殻 `realLogShell` へのリンクとして
束ねる。これは対数リンクのモノ解析的(値群・体積)成分である。単数部の解析的対数
(`logOnePlus`)はノルム保存写像として `realLogShell_analytic` に搭載
―― その加法性のみが既知の残余(冪級数の合成恒等式)。 -/
noncomputable def realLogLink : LogLink ℚ_[11]ˣ realLogShell where
  logMap := realLogMap

/-- 実対数リンクは q-parameter を殻の深さ `1` へ送る: `v₁₁(11) = 1`(値の実計算)。 -/
theorem realLogMap_qParam :
    realLogMap (Additive.ofMul
      (Units.mk0 (11 : ℚ_[11]) (by norm_num))) = 1 := by
  change ((((11 : ℚ_[11])).valuation : ℤ) : ℤ_[11]) = 1
  rw [show ((11 : ℚ_[11])) = ((11 : ℕ) : ℚ_[11]) by norm_cast, Padic.valuation_p]
  norm_num

/-- **単数部の解析的対数(搭載)**: 実対数殻の上で `log(1 + 11y) = 11z`、
`‖z‖ = ‖y‖`(殻の深さ保存 = 体積保存、`Padic/PadicLog.lean` で証明済)。 -/
theorem realLogShell_analytic (y : ℤ_[11]) :
    ∃ z : ℤ_[11],
      IUT.Padic.logOnePlus (((11 : ℕ) : ℚ_[11]) * (y : ℚ_[11]))
        = ((11 : ℕ) : ℚ_[11]) * (z : ℚ_[11]) ∧
      ‖(z : ℚ_[11])‖ = ‖(y : ℚ_[11])‖ :=
  IUT.Padic.logOnePlus_shell (p := 11) (by norm_num) y

/-! ## 5. 実 F-プライム縞と実 Θ リンク -/

/-- **実 F-プライム縞**: 各素点に実際の `Π_v = G_v = Gal(ℚ̄_p/ℚ_p)`(緩 π₁ 未構築ゆえ
正則構造は基礎体のもの ―― honest)、`O▷` 側単項式 `Mon = ℚ̄_pˣ`、実 Galois 作用。
[IUT-I] Def 5.2 の F-プライム縞の実現(整構造 `O▷ ⊆ Mon` は
`Arithmetic/RealFrobenioid.lean` の `integralUnits` で装備済)。 -/
noncomputable def realFStrip : FPrimeStrip.{0} RationalPlaces where
  toDPrimeStrip := realDStrip
  Mon := fun v => letI := Fact.mk v.2; (AlgebraicClosure ℚ_[v.1])ˣ
  commMonoidMon := fun v => by
    letI := Fact.mk v.2
    exact inferInstanceAs (CommMonoid (AlgebraicClosure ℚ_[v.1])ˣ)
  action := fun v => by
    letI := Fact.mk v.2
    exact galoisUnitsAction v.1

/-- **実 Θ リンク**: 実 F-プライム縞(第 n 劇場)と実 F-プライム縞(第 n+1 劇場)を
**モノ解析的核 `D⊢`**(実際の `Gal(ℚ̄_p/ℚ_p)` の族)でのみ同一視する貼り合わせ
([IUT-II] Thm A (iii) の `Θ×μ`-link の骨格)。恒等代表を与える ―― 実物は
full poly-isomorphism(全同型の軌道)であり、恒等はその代表点(honest)。
正則構造(`Π_v`・単項式)を保存しない点がスキーム論の枠外である所以。 -/
noncomputable def realThetaLink : ThetaLink realFStrip realFStrip :=
  DhPrimeStripEquiv.refl _

/-! ## 6. 総合判定 -/

/-- `l = 7` の適格性: `7 ∤ 11`(= `7 ∤ Δ = −11`、7 は good な素数)。 -/
theorem seven_good : ¬ (7 ∣ 11) := by decide

/-- **統合 witness の型**: 実曲線から構成された全装置を単一レコードに束ねる。 -/
structure IntegrationWitness where
  /-- 実 Hodge 劇場(`l = 7`)。 -/
  theater : IUT.HodgeTheater.Full
  /-- 実対数殻。 -/
  shell : LogShell.{0}
  /-- 実対数リンク(値群成分)。 -/
  logLink : LogLink ℚ_[11]ˣ shell
  /-- 実 Θ リンク。 -/
  thetaLink : ThetaLink realFStrip realFStrip

/-- **統合判定テスト(構成部)**: 実曲線 11a3 の算術に基づく Hodge 劇場・対数殻・
対数リンク・Θ リンクの全てが実際に構成される ―― この定義が型検査を通ること自体が
判定テストの合格である。 -/
noncomputable def integrationWitness : IntegrationWitness where
  theater := realHodgeTheater
  shell := realLogShell
  logLink := realLogLink
  thetaLink := realThetaLink

/-- **統合判定テスト(数値部)**: 実曲線 11a3 の局所算術の全計算を束ねる ――
判別式・c₄・j-不変量・11 進ノルム(Tate 判定)・q の殻の正規化対数体積。 -/
theorem integration_test_passes :
    curve11a3.Δ = -11
    ∧ curve11a3.j = -4096 / 11
    ∧ ‖(curve11a3.Δ : ℚ_[11])‖ = (11 : ℝ)⁻¹
    ∧ ‖(curve11a3.c₄ : ℚ_[11])‖ = 1
    ∧ ‖(curve11a3.j : ℚ_[11])‖ = 11
    ∧ IUT.Padic.logVol (curve11a3.Δ : ℚ_[11]) = -Real.log 11 :=
  ⟨curve11a3_Δ, curve11a3_j, curve11a3_Δ_norm, curve11a3_c₄_norm,
    curve11a3_j_norm, curve11a3_Δ_logVol⟩

end IUT.Arithmetic

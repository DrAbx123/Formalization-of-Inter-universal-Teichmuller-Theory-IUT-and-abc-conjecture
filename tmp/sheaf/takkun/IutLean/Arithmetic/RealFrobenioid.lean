import Mathlib
import tmp.sheaf.takkun.IutLean.Frobenioid.Basic
import tmp.sheaf.takkun.IutLean.Multiradial.Thm311
import tmp.sheaf.takkun.IutLean.Arithmetic.RealHodgeTheater

/-!
# 実フロベニオイド — スペクトルノルムによる O▷ 整構造と実次数

底本: [FrdI] / [IUT-I] §3(フロベニオイド)、[IUT-IV] §1(体積計算)。

`realHodgeTheater` の局所単項式 `Mon = (ℚ̄_p)ˣ` は従来「整構造 O▷ 未装備」だった。
Mathlib の `PadicAlgCl p`(= `AlgebraicClosure ℚ_[p]` の **abbrev**、スペクトルノルム付き
`NormedField`、`Mathlib.NumberTheory.Padics.Complex`)により、**実 Hodge 劇場の既存の型の上に**
整構造とフロベニオイド次数が装備できる:

## 証明済(全て標準公理のみ)

* `integralUnits p`: **O▷ 整構造** = `{u : ℚ̄_pˣ | ‖u‖ ≤ 1}`(スペクトルノルムの単位球の
  非零元)が `(PadicAlgCl p)ˣ` の部分モノイドをなす(ultrametric 不要、乗法性のみ);
* `norm_coe_eq_one_of_isUnit`: O▷ のモノイド単数はノルム 1(`O× = {‖·‖ = 1}` の半分)――
  次数が値モノイド `O▷/O×` に降下する理由;
* `realFrobenioid p : Model`: **実フロベニオイド** ―― `deg = −log‖·‖` を
  `Associates`(値モノイド)上の準同型として構成した `Frobenioid.Model` インスタンス。
  **抽象フロベニオイド論(`Frobenioid/Basic.lean`・`Thm311.lean` Part 1)が実際の
  `ℚ̄_p` の数論に接地した**;
* `degree_qFrob`: 実 q-parameter(`q = p`)の次数 `= log p > 0`;
* **`real_theta_vol_11a3`(capstone)**: `theta_vol_derivation`(Thm 3.11 (i)(b) の
  送信側体積導出)を実フロベニオイド(`p = 11`)で実行 ――
  **送信側ピン `volS(Θ標) = arithFactor · logq` が実際の `ℚ̄₁₁` のスペクトルノルムから
  実数値 `(14/3)·log 11` として導出される**(`Thm311Transcription.theta_vol` の実現);
* `realGaussianStrip_qParam_integral` / `realThetaValue_integral`: 実 Hodge 劇場の
  q-parameter と全テータ値 `q^{j²}` は O▷ に属する(**整構造の装備**)。

## 残余(honest)

* `O×µ`(捩れ = 1 の巾根で割った商)の実対象上の具体計算;
* 対数リンクとの両立(`logOnePlus` は `ℚ_p` 上のみ構築済 ―― `ℂ_[p]` = 完備化上への
  一般化が受け皿、`PadicComplex` は完備 + ultrametric ゆえ同じ構成が通る);
* 受信側(対数殻テンソルパケット)の体積上界 = `hull_bound` 本体(Prop 1.1–1.9 の残り)。
-/

namespace IUT.Arithmetic

open IUT.Frobenioid Finset

variable (p : ℕ) [hp : Fact p.Prime]

/-- **O▷ 整構造**: スペクトルノルムの単位球の非零元
`{u : ℚ̄_pˣ | ‖u‖ ≤ 1}` のなす部分モノイド([FrdI] の `O▷_v = {a : 0 < |a| ≤ 1}`)。 -/
def integralUnits : Submonoid (PadicAlgCl p)ˣ where
  carrier := {u : (PadicAlgCl p)ˣ | ‖(u : PadicAlgCl p)‖ ≤ 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, norm_mul] at *
    calc ‖(a : PadicAlgCl p)‖ * ‖(b : PadicAlgCl p)‖
        ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

@[simp] lemma mem_integralUnits {u : (PadicAlgCl p)ˣ} :
    u ∈ integralUnits p ↔ ‖(u : PadicAlgCl p)‖ ≤ 1 := Iff.rfl

/-- O▷ のモノイド単数はノルム 1: `u` が O▷ の中で可逆なら逆元も整ゆえ
`‖u‖·‖u⁻¹‖ = 1` かつ両者 `≤ 1` から `‖u‖ = 1`。`O× = {‖·‖ = 1}` の内容であり、
次数 `−log‖·‖` が値モノイド `O▷/O×` に降下する理由。 -/
theorem norm_coe_eq_one_of_isUnit {x : ↥(integralUnits p)} (hx : IsUnit x) :
    ‖((x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 := congrArg
    (fun z : ↥(integralUnits p) => ((z : (PadicAlgCl p)ˣ) : PadicAlgCl p)) (Units.mul_inv u)
  simp only [Submonoid.coe_mul, Units.val_mul, OneMemClass.coe_one, Units.val_one] at h1
  have hnorm := congrArg norm h1
  rw [norm_mul, norm_one] at hnorm
  have ha : ‖(((u : ↥(integralUnits p)) : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ ≤ 1 :=
    (u : ↥(integralUnits p)).2
  have hb : ‖(((↑u⁻¹ : ↥(integralUnits p)) : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ ≤ 1 :=
    (↑u⁻¹ : ↥(integralUnits p)).2
  have h2 : ‖(((u : ↥(integralUnits p)) : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖
        * ‖(((↑u⁻¹ : ↥(integralUnits p)) : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖
      ≤ ‖(((u : ↥(integralUnits p)) : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hb
  rw [hnorm] at h2
  linarith

/-- 次数の前駆準同型: `O▷ →* (ℝ, +)`, `x ↦ −log‖x‖`(整な非零元ゆえ `≥ 0`)。 -/
noncomputable def degAux : ↥(integralUnits p) →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (-Real.log ‖((x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖)
  map_one' := by
    simp
  map_mul' x y := by
    have hx : ((x : (PadicAlgCl p)ˣ) : PadicAlgCl p) ≠ 0 := Units.ne_zero _
    have hy : ((y : (PadicAlgCl p)ˣ) : PadicAlgCl p) ≠ 0 := Units.ne_zero _
    simp only [Submonoid.coe_mul, Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]
    rw [neg_add, ofAdd_add]

/-- 単数では次数の前駆は自明(`‖単数‖ = 1` ゆえ `−log 1 = 0`)。 -/
theorem degAux_of_isUnit {x : ↥(integralUnits p)} (hx : IsUnit x) : degAux p x = 1 := by
  change Multiplicative.ofAdd (-Real.log ‖((x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖) = 1
  rw [norm_coe_eq_one_of_isUnit p hx, Real.log_one, neg_zero, ofAdd_zero]

/-- **実次数**: 値モノイド `O▷/O× = Associates O▷` 上の数論的次数
`deg = −log‖·‖`(単数がノルム 1 ゆえ well-defined)。 -/
noncomputable def realDeg : Associates ↥(integralUnits p) →* Multiplicative ℝ where
  toFun := Quotient.lift (fun x => degAux p x) (by
    intro a b hab
    obtain ⟨u, hu⟩ := hab
    have : degAux p b = degAux p a * degAux p ↑u := by
      rw [← hu, map_mul]
    rw [this, degAux_of_isUnit p u.isUnit, mul_one])
  map_one' := map_one (degAux p)
  map_mul' x y := by
    refine Quotient.inductionOn₂ x y fun a b => ?_
    exact map_mul (degAux p) a b

@[simp] theorem realDeg_mk (x : ↥(integralUnits p)) :
    realDeg p (Associates.mk x) = degAux p x := rfl

/-- **実フロベニオイド**: `O▷ = {u : ℚ̄_pˣ | ‖u‖ ≤ 1}`(スペクトルノルム)、
`deg = −log‖·‖` の `Frobenioid.Model`。抽象フロベニオイド論の実 p 進数論への接地。 -/
noncomputable def realFrobenioid : Model where
  base := ⟨↥(integralUnits p)⟩
  deg := realDeg p

/-- 素数 `p` の `ℚ̄_p` でのノルム = `p⁻¹`(スペクトルノルムは `ℚ_p` のノルムを延長)。 -/
lemma norm_natCast_prime : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [show ((p : ℕ) : PadicAlgCl p) = (((p : ℕ) : ℚ_[p]) : PadicAlgCl p) from
      (map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p).symm,
    PadicAlgCl.norm_extends, Padic.norm_p]

/-- **実 q-parameter の O▷ 代表**: `q = p ∈ ℚ̄_pˣ` はノルム `p⁻¹ ≤ 1` ゆえ整構造に属する。 -/
noncomputable def qFrob : ↥(integralUnits p) :=
  ⟨Units.mk0 ((p : ℕ) : PadicAlgCl p)
      (Nat.cast_ne_zero.mpr hp.out.ne_zero),
   by
     change ‖((p : ℕ) : PadicAlgCl p)‖ ≤ 1
     rw [norm_natCast_prime]
     have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
     exact le_of_lt (inv_lt_one_of_one_lt₀ h1)⟩

/-- **実 q-parameter の次数 = `log p > 0`**: 実フロベニオイドの内部で
`deg(q) = −log‖p‖ = −log(p⁻¹) = log p`。 -/
theorem degree_qFrob :
    (realFrobenioid p).degree ((realFrobenioid p).base.valueMap (qFrob p)) = Real.log p := by
  change Multiplicative.toAdd (realDeg p (Associates.mk (qFrob p))) = Real.log p
  rw [realDeg_mk]
  change -Real.log ‖((p : ℕ) : PadicAlgCl p)‖ = Real.log p
  rw [norm_natCast_prime, Real.log_inv, neg_neg]

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- **送信側ピンの実導出(capstone)**: Thm 3.11 (i)(b) の送信側体積導出
`theta_vol_derivation` を**実フロベニオイド**(`p = 11`、曲線 11a3 の素点)で実行 ――
Gaussian 単項式 `{q^{j²}}` のプロセッション正規化次数が、実際の `ℚ̄₁₁` の
スペクトルノルムから `arithFactor · logq = (14/3)·log 11` として導出される。
`Thm311Transcription.theta_vol`(送信側ピン)が実対象の上で実現された。 -/
theorem real_theta_vol_11a3 (eta D : ℝ) (heta : 0 ≤ eta) (hD : 0 ≤ D) :
    (∑ j ∈ range (lStar 7 + 1),
        (realFrobenioid 11).degree
          (((realFrobenioid 11).base.valueMap (qFrob 11)) ^ (j ^ 2))) / ((lStar 7 : ℕ) : ℝ)
      = (curve11a3Data eta D heta hD).arithFactor * (curve11a3Data eta D heta hD).logq := by
  have h := IUT.Multiradial.theta_vol_derivation (realFrobenioid 11)
    ((realFrobenioid 11).base.valueMap (qFrob 11)) 7 ⟨3, by norm_num⟩ (le_refl 7)
  rw [h, degree_qFrob]
  have h1 : (curve11a3Data eta D heta hD).arithFactor = ((7 : ℝ) * ((7 : ℝ) + 1)) / 12 := by
    unfold ArithmeticData.arithFactor curve11a3Data
    norm_num
  have h2 : (curve11a3Data eta D heta hD).logq = Real.log 11 := by
    unfold ArithmeticData.logq curve11a3Data
    norm_num
  rw [h1, h2]
  norm_num

/-! ## 実 Hodge 劇場への整構造の装備 -/

/-- **実 Hodge 劇場の q-parameter は O▷ に属する**: `realGaussianStrip` の各素点の
q-parameter(`= p`)はスペクトルノルム `≤ 1` ―― 従来「整構造未装備」だった
`Mon = ℚ̄_pˣ` に、その部分モノイドとしての整構造が実際に装備された。 -/
theorem realGaussianStrip_qParam_integral (v : RationalPlaces) :
    letI := Fact.mk v.2
    realGaussianStrip.qParam v ∈ integralUnits v.1 := by
  letI := Fact.mk v.2
  change ‖((v.1 : ℕ) : PadicAlgCl v.1)‖ ≤ 1
  rw [norm_natCast_prime]
  have h1 : (1 : ℝ) < (v.1 : ℝ) := by exact_mod_cast v.2.one_lt
  exact le_of_lt (inv_lt_one_of_one_lt₀ h1)

/-- **実テータ値は全て O▷ に属する**: `q^{j²}` は整元の巾ゆえ整(`pow_mem`)。
Gaussian 単項式(Thm 3.11 の分裂モノイド)が実整構造の中に住むことの確認。 -/
theorem realThetaValue_integral (v : RationalPlaces) (j : ℤ) :
    letI := Fact.mk v.2
    realGaussianStrip.thetaValueAt v j ∈ integralUnits v.1 := by
  letI := Fact.mk v.2
  change realGaussianStrip.qParam v ^ (IUT.Theta.gaussExp j).toNat ∈ integralUnits v.1
  exact pow_mem (realGaussianStrip_qParam_integral v) _

end IUT.Arithmetic

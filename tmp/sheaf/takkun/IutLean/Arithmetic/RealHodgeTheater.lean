import Mathlib
import tmp.sheaf.takkun.IutLean.HodgeTheater.Defs
import tmp.sheaf.takkun.IutLean.Arithmetic.CurveInstance

/-!
# 実 Hodge 劇場 — 本物の局所 Galois 群・本物の q-parameter による構築

底本: [IUT-I] Def 5.2, Def 6.13 / 本プロジェクトのプライム縞インフラ。

これまでの Hodge 劇場の witness は toy(自明群 `PUnit`・`Multiplicative ℤ`)だった。
本モジュールは Mathlib の実在する p 進数論(`ℚ_[p]`・`AlgebraicClosure`)を用いて、
**実際の数論的対象**からなる素点縞系と Hodge 劇場を構築する:

## 実物である部分
* **素点の集合** = ℚ の素数全体(`RationalPlaces`);
* **局所絶対 Galois 群** `G_p = Gal(ℚ̄_p/ℚ_p)`(実際の `AlgebraicClosure ℚ_[p]` の
  `ℚ_[p]`-代数自己同型群 ―― IUT の `G_v` の本物);
* **局所単項式への Galois 作用**: `G_p` の `ℚ̄_pˣ` への実際の作用(`Units.mapEquiv`);
* **q-parameter**: 素点 `11` で `q = 11 ∈ ℚ̄₁₁ˣ` ―― 曲線 11a3 の Tate parameter の代表
  (`v₁₁(q) = 1` は `curve11a3_Δ = −11` の計算と整合)。**テータ値 `q^{j²} = 11^{j²}` は
  実際の体 `ℚ̄₁₁` の元**であり、その非退化性(`j ≠ 0 ⟹ 11^{j²} ≠ 1`)は標数 0 で証明される。

## まだ骨格である部分(honest)
* `Π_v = G_v`(曲線の緩基本群 `π₁^tp(X_v)` は未構築 ―― 正則構造は基礎体のもの);
* 対称化同型は定値ラベル系上の `refl`(実物は `Π_X` 内の共役から生じる);
* `Mon = ℚ̄_pˣ` 全体(閉包の整数環 `O▷` の付値構造は未装備);
* アルキメデス素点は省略。

それでも: **IUT の素点縞・Hodge 劇場が、初めて実際の絶対 Galois 群と実際の代数閉包の上に
立った** ―― 判定テストの受験(Thm 3.11 の転写)が行われるべき舞台の最初の実体である。
-/

namespace IUT.Arithmetic

open IUT.Frobenioid

/-- **有限素点の集合** = ℚ の素数全体。 -/
abbrev RationalPlaces : Type := {p : ℕ // p.Prime}

/-- **局所絶対 Galois 群** `G_p = Gal(ℚ̄_p/ℚ_p)`(実物:
`AlgebraicClosure ℚ_[p]` の `ℚ_[p]`-代数自己同型群)。 -/
abbrev LocalGalois (p : ℕ) [Fact p.Prime] : Type :=
  AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]

/-- 代数閉包 `ℚ̄_p` は標数 0(`ℚ_[p]` からの単射代数写像による)。 -/
noncomputable instance instCharZeroClosure (p : ℕ) [Fact p.Prime] :
    CharZero (AlgebraicClosure ℚ_[p]) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective

/-- **Galois 作用の実物**: `G_p` の `ℚ̄_pˣ` への作用(体自己同型が単数群に誘導する
乗法的自己同型、`Units.mapEquiv`)。 -/
noncomputable def galoisUnitsAction (p : ℕ) [Fact p.Prime] :
    LocalGalois p →* MulAut (AlgebraicClosure ℚ_[p])ˣ where
  toFun σ := Units.mapEquiv σ.toRingEquiv.toMulEquiv
  map_one' := by
    ext u
    rfl
  map_mul' σ τ := by
    ext u
    rfl

/-- **実 D-プライム縞**: 各素数 `p` に実際の局所絶対 Galois 群 `Gal(ℚ̄_p/ℚ_p)` を置いた
D-プライム縞(`Π_v = G_v`: 曲線の緩基本群は未構築ゆえ正則構造は基礎体のもの)。 -/
noncomputable def realDStrip : DPrimeStrip.{0} RationalPlaces where
  Pi := fun v => letI := Fact.mk v.2; LocalGalois v.1
  groupPi := fun v => by letI := Fact.mk v.2; exact inferInstanceAs (Group (LocalGalois v.1))
  G := fun v => letI := Fact.mk v.2; LocalGalois v.1
  groupG := fun v => by letI := Fact.mk v.2; exact inferInstanceAs (Group (LocalGalois v.1))
  proj := fun _ => MonoidHom.id _
  proj_surjective := fun _ => Function.surjective_id

/-- **実 Gaussian プライム縞**: 実際の Galois 群・実際の `ℚ̄_pˣ`・実際の Galois 作用・
実際の q-parameter(各素点で `q = p`、特に `11` では曲線 11a3 の Tate parameter 代表)。 -/
noncomputable def realGaussianStrip : GaussianPrimeStrip.{0, 0, 0} RationalPlaces where
  G := fun v => letI := Fact.mk v.2; LocalGalois v.1
  group := fun v => by letI := Fact.mk v.2; exact inferInstanceAs (Group (LocalGalois v.1))
  Mon := fun v => letI := Fact.mk v.2; (AlgebraicClosure ℚ_[v.1])ˣ
  commMonoidMon := fun v => by
    letI := Fact.mk v.2
    exact inferInstanceAs (CommMonoid (AlgebraicClosure ℚ_[v.1])ˣ)
  action := fun v => letI := Fact.mk v.2; galoisUnitsAction v.1
  qParam := fun v =>
    letI := Fact.mk v.2
    Units.mk0 ((v.1 : ℕ) : AlgebraicClosure ℚ_[v.1])
      (Nat.cast_ne_zero.mpr v.2.pos.ne')

/-- **テータ値の非退化性(実物)**: 素点 `11` で、`j ≠ 0` ならテータ値
`11^{j²} ∈ ℚ̄₁₁ˣ` は `1` でない ―― 標数 0 の体で `11` は無限位数を持つ。 -/
theorem realGaussian_nondegenerate :
    ∃ v : RationalPlaces, ∀ j : ℤ, j ≠ 0 →
      realGaussianStrip.thetaValueAt v j ≠ 1 := by
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine ⟨⟨11, by norm_num⟩, ?_⟩
  intro j hj h1
  have hN : (IUT.Theta.gaussExp j).toNat ≠ 0 := by
    have h2 : 0 < j ^ 2 := lt_of_le_of_ne (sq_nonneg j) (Ne.symm (pow_ne_zero 2 hj))
    unfold IUT.Theta.gaussExp
    omega
  apply hN
  -- thetaValueAt は定義的に qParam ^ N(defeq 型注釈で取り出す)
  have h2 : (Units.mk0 ((11 : ℕ) : AlgebraicClosure ℚ_[11])
        (Nat.cast_ne_zero.mpr (by norm_num)))
      ^ (IUT.Theta.gaussExp j).toNat = 1 := h1
  have h3 := congrArg Units.val h2
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h3
  -- h3 : ((11:ℕ):ℚ̄₁₁)^N = 1
  have h4 : ((11 ^ (IUT.Theta.gaussExp j).toNat : ℕ) : AlgebraicClosure ℚ_[11])
      = ((1 : ℕ) : AlgebraicClosure ℚ_[11]) := by
    rw [Nat.cast_pow, Nat.cast_one]
    exact h3
  have h5 : (11 : ℕ) ^ (IUT.Theta.gaussExp j).toNat = 1 := Nat.cast_injective h4
  rcases Nat.pow_eq_one.mp h5 with h6 | h6
  · omega
  · exact h6

/-- **実素点縞系**: 実際の局所 Galois 群・実際の代数閉包・実際の q-parameter からなる
Hodge 劇場の素点縞系(対称化同型は定値ラベル上の `refl` ―― 実物の対称化は `Π_X` の
共役から生じ、緩基本群の構築後に置換される)。 -/
noncomputable def realPrimeStripSystem (l : ℕ) [Fact l.Prime] :
    HodgeTheater.PrimeStripSystem l where
  V := RationalPlaces
  addSystem := constantLabeledSystem RationalPlaces (LabCuspPM l) (GeoSym l) realDStrip
  mulSystem := constantLabeledSystem RationalPlaces (LabCusp l) (LabCusp l) realDStrip
  gaussian := realGaussianStrip
  glue := fun _ => ⟨fun _ => MulEquiv.refl _⟩
  nondegenerate := realGaussian_nondegenerate

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- **実 Hodge 劇場**: `l = 7`(曲線 11a3 に適合: `7 ∤ Δ = −11`)と実素点縞系による
Θ±ellNF Hodge 劇場 ―― **実際の絶対 Galois 群 `Gal(ℚ̄_p/ℚ_p)`・実際の代数閉包・
実際の q-parameter の上に立つ最初の Hodge 劇場**。判定テストの受験(Thm 3.11 の転写)が
行われるべき舞台の実体化の第一歩。 -/
noncomputable def realHodgeTheater : HodgeTheater.Full where
  add :=
    { l := 7
      l_ge_five := by norm_num
      primeStrips := realPrimeStripSystem 7 }
  mul :=
    { l := 7
      l_ge_five := by norm_num
      primeStrips := realPrimeStripSystem 7 }
  glue := rfl

end IUT.Arithmetic

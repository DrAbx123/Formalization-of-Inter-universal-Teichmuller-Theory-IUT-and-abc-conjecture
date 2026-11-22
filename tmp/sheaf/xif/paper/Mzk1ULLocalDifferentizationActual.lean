/-
# 逐位（per-vQ）different 的局部化层：指数 `d_v`、per-place ≤ global、AtPrime 义务

david 的 per-vQ 局部对象需要 `𝔇_{L/F}` 在每一位 `P` 上的指数 `d_P = ord_P(𝔇)`
（论文的 `d_vQ`）以及「局部 ≤ 全局」的比较。树内没有现成件：
`Mzk1ULLocalDifferentizationInterfaceActual` 只有数论包装和一个 `Prop := True` 占位。

本文件（全部真证；donor = `Heights.Different.NumberField` + Mathlib）：

* `differentExponent`（= `d_P`）与谱刻画 `P^n ∣ 𝔇 ↔ n ≤ d_P`、`0 < d_P ↔ P ∣ 𝔇`；
* `differentExponent_eq_zero_iff_unramified`：`d_P = 0 ↔ 𝔇` 在 `P` 处非分歧（Mathlib `dvd_differentIdeal_iff`）；
* `localDeltaLog`：逐位对数贡献 `d_P · log|N P|`，非负；
* **per-place ≤ global**：`localDeltaLog P ≤ log|N 𝔇|`，以及 david 的归一化版本
  `diffTerm P ≤ log|N 𝔇| / [L:ℚ]`；
* 逐位分解 `∑ᶠ P, localDeltaLog P = log|N 𝔇|`（donor 的 `log_absNorm_eq_finsum`）；
* **显式义务** `differentLocalizationObligation`：`differentIdeal` 与局部化交换
  （AKLB 的 trace-dual 局部化），并给出其可用推论（局部 different 非零）。

## 待补（Mathlib 4.32 缺件，已在 `AUDIT_LEDGER` 计划中）

`Ideal.map (algebraMap B B_Q) (differentIdeal A B) = differentIdeal A_p B_Q`（AKLB，
`p = Q.under A`）。缺的是 `Submodule.traceDual` 与 `IsLocalization` 的交换律：
Mathlib 只有 `Algebra.trace_localization`（`RingTheory/Localization/NormTrace.lean`），
没有 `Submodule.IsLocalized` / `IsLocalization.localizedSubmodule` / `Module.IsLocalized`
的子模版本，也没有 `FractionalIdeal.extendedHom` 与 `FractionalIdeal.dual` 的交换律
（`grep differentIdeal` 在 Mathlib 只命中 `DedekindDomain/Different.lean`、`DedekindDomain/LinearDisjoint.lean`、
`NumberField/Discriminant/Different.lean`、`Cyclotomic/Basic.lean`，均无局部化命题）。
义务入库后，把 `differentLocalizationObligation` 的定义体改成定理即可。
-/
import tmp.sheaf.lana.heights.Heights.Different.NumberField
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false

-- 让 `FractionRing (𝓞 F)` 与 `FractionRing (𝓞 L)` 之间获得 `Algebra` 实例
-- （与 Mathlib `RingTheory/DedekindDomain/Different.lean` 的写法一致）。
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual

open NumberField IsDedekindDomain Heights.Different

variable {F : Type*} [Field F] [NumberField F]
variable {L : Type*} [Field L] [NumberField L] [Algebra F L]

/-! ### 逐位 different 指数 `d_P` -/

/-- 位 `P`（在 `L` 上，相对于 `F`）的 different 指数
`d_P = ord_P(𝔇_{L/F})`，即 david 的 `d_vQ`。 -/
noncomputable def differentExponent (P : HeightOneSpectrum (𝓞 L)) : ℕ :=
  multiplicity P.asIdeal (differentIdeal (𝓞 F) (𝓞 L))

/-- `P^n ∣ 𝔇 ↔ n ≤ d_P`（donor `pow_dvd_iff_le_multiplicity`）。 -/
theorem pow_dvd_iff_le_differentExponent (P : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    P.asIdeal ^ n ∣ differentIdeal (𝓞 F) (𝓞 L) ↔ n ≤ differentExponent (F := F) P := by
  haveI := P.isPrime
  unfold differentExponent
  exact pow_dvd_iff_le_multiplicity (I := differentIdeal (𝓞 F) (𝓞 L)) P.ne_bot
    (differentIdeal_ne_bot' F L)

/-- `0 < d_P ↔ P ∣ 𝔇`：正指数正好是整除 `𝔇` 的位。 -/
theorem differentExponent_pos_iff (P : HeightOneSpectrum (𝓞 L)) :
    0 < differentExponent (F := F) P ↔ P.asIdeal ∣ differentIdeal (𝓞 F) (𝓞 L) := by
  unfold differentExponent
  exact dvd_iff_multiplicity_pos

/-- `d_P ≤ n` 若 `P^{n+1} ∤ 𝔇`（donor `multiplicity_le_of_not_pow_dvd`）。 -/
theorem differentExponent_le_of_not_pow_dvd (P : HeightOneSpectrum (𝓞 L)) (n : ℕ)
    (h : ¬ P.asIdeal ^ (n + 1) ∣ differentIdeal (𝓞 F) (𝓞 L)) :
    differentExponent (F := F) P ≤ n := by
  haveI := P.isPrime
  unfold differentExponent
  exact multiplicity_le_of_not_pow_dvd (I := differentIdeal (𝓞 F) (𝓞 L)) P.ne_bot
    (differentIdeal_ne_bot' F L) h

/-- **`d_P = 0` 恰在非分歧位**：`d_P = 0 ↔ 𝔇` 在 `P` 处非分歧
（Mathlib `dvd_differentIdeal_iff`）。 -/
theorem differentExponent_eq_zero_iff_unramified
    [Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 L))]
    (P : HeightOneSpectrum (𝓞 L)) :
    differentExponent (F := F) P = 0 ↔ Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := by
  haveI := P.isPrime
  constructor
  · intro h0
    by_contra hU
    have hdvd : P.asIdeal ∣ differentIdeal (𝓞 F) (𝓞 L) :=
      dvd_differentIdeal_iff.mpr hU
    have hpos : 0 < differentExponent (F := F) P :=
      (differentExponent_pos_iff (F := F) P).mpr hdvd
    omega
  · intro hU
    by_contra h0
    have hpos : 0 < differentExponent (F := F) P := Nat.pos_of_ne_zero h0
    exact (dvd_differentIdeal_iff.mp ((differentExponent_pos_iff (F := F) P).mp hpos)) hU

/-! ### 逐位对数贡献与 per-place ≤ global -/

/-- 位 `P` 的（未归一）different 对数贡献 `d_P · log|N P|`。 -/
noncomputable def localDeltaLog (P : HeightOneSpectrum (𝓞 L)) : ℝ :=
  (differentExponent (F := F) P : ℝ) * Real.log (Ideal.absNorm P.asIdeal)

theorem localDeltaLog_nonneg (P : HeightOneSpectrum (𝓞 L)) :
    0 ≤ localDeltaLog (F := F) P :=
  mul_nonneg (by positivity) (log_absNorm_nonneg P.asIdeal)

/-- `|N P|^{d_P} ∣ |N 𝔇|`：由 `P^{d_P} ∣ 𝔇` 与 `absNorm` 的乘性。 -/
theorem pow_differentExponent_absNorm_le (P : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm P.asIdeal ^ differentExponent (F := F) P ≤
      Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) := by
  haveI := P.isPrime
  have hdvd : P.asIdeal ^ differentExponent (F := F) P ∣ differentIdeal (𝓞 F) (𝓞 L) :=
    (pow_dvd_iff_le_differentExponent (F := F) P _).mpr le_rfl
  have hle : differentIdeal (𝓞 F) (𝓞 L) ≤ P.asIdeal ^ differentExponent (F := F) P :=
    Ideal.dvd_iff_le.mp hdvd
  have h : Ideal.absNorm P.asIdeal ^ differentExponent (F := F) P ∣
      Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) := by
    rw [← map_pow]
    exact Ideal.absNorm_dvd_absNorm_of_le hle
  exact Nat.le_of_dvd (absNorm_differentIdeal_pos F L) h

/-- **per-place ≤ global**（绝对形式）：`d_P · log|N P| ≤ log|N 𝔇|`。 -/
theorem localDeltaLog_le_log_absNorm (P : HeightOneSpectrum (𝓞 L)) :
    localDeltaLog (F := F) P ≤
      Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) := by
  have hpow := pow_differentExponent_absNorm_le (F := F) (L := L) P
  have hle : ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ differentExponent (F := F) P ≤
      ((Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) : ℕ) : ℝ) := by
    exact_mod_cast hpow
  have hpos : 0 < ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ differentExponent (F := F) P :=
    pow_pos (by exact_mod_cast (one_lt_absNorm P).pos) _
  calc localDeltaLog (F := F) P
      = Real.log (((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ differentExponent (F := F) P) := by
        rw [Real.log_pow, localDeltaLog]
    _ ≤ Real.log ((Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) : ℕ) : ℝ) :=
        Real.log_le_log hpos hle

/-- **per-place ≤ global**（david 的归一化 `d_vQ`/`[L:ℚ]` 形式）。 -/
theorem diffTerm_le_global (P : HeightOneSpectrum (𝓞 L)) :
    diffTerm F L P ≤
      Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) / (Module.finrank ℚ L : ℝ) := by
  have h := localDeltaLog_le_log_absNorm (F := F) (L := L) P
  have hterm : diffTerm F L P = localDeltaLog (F := F) P / (Module.finrank ℚ L : ℝ) := rfl
  rw [hterm]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- 逐位贡献的（可数）和 = 全局 different 对数（donor `log_absNorm_eq_finsum`）。 -/
theorem finsum_localDeltaLog :
    (∑ᶠ P : HeightOneSpectrum (𝓞 L), localDeltaLog (F := F) P) =
      Real.log (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) := by
  rw [log_absNorm_eq_finsum (I := differentIdeal (𝓞 F) (𝓞 L)) (differentIdeal_ne_bot' F L)]
  rfl

/-! ### 显式义务：`differentIdeal` 与局部化交换（AKLB） -/

section Obligation

variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable {Ap : Type*} [CommRing Ap] [IsDomain Ap] [IsIntegrallyClosed Ap] [Algebra A Ap]
variable {Bq : Type*} [CommRing Bq] [IsDomain Bq] [IsDedekindDomain Bq] [Algebra B Bq]
  [Algebra Ap Bq] [Module.IsTorsionFree Ap Bq]

/-- **显式义务**（AKLB 的 different 局部化）：`𝔇_{B/A}` 在 `B_Q` 处的局部化等于
`𝔇_{B_Q/A_p}`。

应用时 `A = 𝓞 F_mod`、`B = 𝓞 F`、`Ap = Localization.AtPrime p`、
`Bq = Localization.AtPrime Q`（`p = Q.under A`），`[Algebra Ap Bq]` 由
`Localization.AtPrime.algebraOfLiesOver` 提供。

**待补**：`Submodule.traceDual` 与 `IsLocalization` 的交换律；Mathlib 缺
`Submodule.IsLocalized` / `IsLocalization.localizedSubmodule` 与
`FractionalIdeal.extendedHom` 对 `FractionalIdeal.dual` 的交换律。义务入库后
本定义应改成定理（陈述已按最终形状固定，可直接替换）。 -/
def differentLocalizationObligation : Prop :=
  Ideal.map (algebraMap B Bq) (differentIdeal A B) = differentIdeal Ap Bq

/-- 由义务得到：局部化后的 different 非零（david 的局部对象是真对象，不退化为 `⊥`）。 -/
theorem map_differentIdeal_ne_bot_of_obligation
    [Module.Finite Ap Bq] [Algebra.IsSeparable (FractionRing Ap) (FractionRing Bq)]
    (h : differentLocalizationObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq)) :
    Ideal.map (algebraMap B Bq) (differentIdeal A B) ≠ ⊥ := by
  unfold differentLocalizationObligation at h
  rw [h]
  exact differentIdeal_ne_bot

/-- 由义务得到 `≤` 方向（供局部化链使用）。 -/
theorem map_differentIdeal_le_of_obligation
    (h : differentLocalizationObligation (A := A) (B := B) (Ap := Ap) (Bq := Bq)) :
    Ideal.map (algebraMap B Bq) (differentIdeal A B) ≤ differentIdeal Ap Bq := by
  unfold differentLocalizationObligation at h
  exact h.le

end Obligation

#print axioms differentExponent
#print axioms pow_dvd_iff_le_differentExponent
#print axioms differentExponent_pos_iff
#print axioms differentExponent_le_of_not_pow_dvd
#print axioms differentExponent_eq_zero_iff_unramified
#print axioms localDeltaLog
#print axioms localDeltaLog_nonneg
#print axioms pow_differentExponent_absNorm_le
#print axioms localDeltaLog_le_log_absNorm
#print axioms diffTerm_le_global
#print axioms finsum_localDeltaLog
#print axioms differentLocalizationObligation
#print axioms map_differentIdeal_ne_bot_of_obligation
#print axioms map_differentIdeal_le_of_obligation

end LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual

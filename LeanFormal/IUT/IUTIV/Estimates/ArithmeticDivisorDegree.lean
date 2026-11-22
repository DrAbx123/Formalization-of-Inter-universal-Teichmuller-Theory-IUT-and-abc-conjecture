/-
# IUT IV Definition 1.9：算术除子、度与归一化度（算术除子/度数层）

论文出处（正文行号均为 `papers\motizuki_corpus\text\Inter-universal Teichmuller Theory IV.txt` 的行）：
- Definition 1.9（L1204 起）：V(F) = V(F)_non ⊔ V(F)_arc；R-算术除子 = V(F) 上的有限形式和；
  deg_F：V(F)_non ∋ v ↦ log(q_v)，V(F)_arc ∋ v ↦ 1；deg := (1/[F:Q])·deg_F；
  拉回 a|K 的归一化度不变（原文：“defined in the evident fashion”，未显式给系数约定）。
- Definition 1.9 (ii)（L~1236）：E ⊆ V(F) 为某 vQ ∈ V(Q) 之上的纤维；a_E = 支撑在 E 的部分；
  deg_E(a) = deg(a_E) / Σ_{v∈E} [F_v : Q_{vQ}]。

本文件的落点（承接 `outsider-survey-estimates-20261016.md` §3.1/§3.2/§5 与 root 2026-10-16 任务包②）：
- 具体对象：`IUTIVPlace F`（有限位点 = HeightOneSpectrum (𝓞 F)；阿基米德位点 = InfinitePlace F），
  `IUTIVArithmeticDivisor F := IUTIVPlace F →₀ ℝ`（Finsupp）。q_v 用 `Ideal.absNorm`（= 剩余域基数，
  见 `IUTIVPlace.absNorm_eq_cardQuot`）。
- deg_F 线性（由 Finsupp.linearCombination 构造，线性免费）；ndeg 为其归一化。
- 拉回：**约定取系数 (a|K)_w = c_v · e_w**，其中有限位点 w 上 e_w = 分歧指数
  `Ideal.ramificationIdx`（阿基米德位点 w 上 e_w = 局部次数 = `InfinitePlace.inertiaDeg`）。
  该约定下 deg_K(a|K) = [K:F]·deg_F(a)（论文 Def 1.9 的“evident fashion”未写明系数；本约定是
  使论文随后的归一化度不变性质成立的标准除子拉回约定，见 `deg_pullback` 并显式标注此选择）。
- 定理 `deg_pullback`、`ndeg_pullback`：前者的逐纤维和用 Mathlib 的两条基本恒等式证明
  （有限位点：`Ideal.sum_ramification_inertia_eq_finrank`；阿基米德位点：
  `NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`），加 `Ideal.absNorm_pow_inertiaDeg`
  （q_w = q_v^{f_w}）与 `Module.finrank_mul_finrank`（[K:Q] = [F:Q]·[K:F]）。
- C1（Def 1.9 (ii) 的 “Thus”）已落地（`section FiberDegreeLedger`，2026-10-16）：
  精确不变式落在未归一化分子读数 `eDegreeUnnormalized`（分子 deg_F(a_E)）；
  字面（归一化分子）读数 `eDegree` 满足因子律 `eDegree_{E|K}(a|K) = eDegree_E(a)/[K:F]`
  （字面等式差 [K:F] 因子，两独立算例见 2026-10-16 侦察笔记；两种读数均已 Lean 化）。
  C2（纤维归一化常数 Σ_{v∈E}[F_v:Q_{vQ}]）见 `section FiberNormalizationConstants`（已证）。

## 决定登记（rec3，root 2026-10-16）
hweightvol/hpoint 的算术侧按 Def 1.9 + Remark 1.10.1（Explicit estimates L~884：q-参数有效算术除子的
ndeg = h_non(j(E))，引 [Silv1] VII.5.5）**论文化**；源侧保留几何卡（不动几何侧文件）。
本文件提供算术侧对象的落点（除子、度、局部次数），供上层字典卡消费者接入。

## Explicit estimates 叶引理（同文件，承接任务包①的小额项）
- Explicit Lemma 1.11（L897）：0 ≤ a − log a − 1 及线性化推论（两处均已证）。
- Explicit Lemma 1.3（L486）代数部分：论文引用的两个“易验证”事实与 (i)/(iv) 的逐点/加权和内核对
  （完整 h□-层陈述需要 V(F) 高度层，缩减显式标注于对应 docstring）。
-/

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.ProductFormula
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegreeGlobal

open scoped NumberField Classical
open IsDedekindDomain

noncomputable section

namespace LeanFormal.IUT.IUTIV.Estimates

section PlacesAndWeights

variable (F : Type*) [Field F] [NumberField F]

/-- IUT IV Def 1.9 的位点类型 V(F) = V(F)_non ⊔ V(F)_arc：
有限位点取素理想（高度一谱 `HeightOneSpectrum (𝓞 F)`），阿基米德位点取 `InfinitePlace F`。 -/
inductive IUTIVPlace where
  | finite : HeightOneSpectrum (𝓞 F) → IUTIVPlace
  | infinite : NumberField.InfinitePlace F → IUTIVPlace

namespace IUTIVPlace

/-- Def 1.9 的 deg_F 权重：v ↦ log(q_v)（有限位点，q_v = 剩余域基数 = `Ideal.absNorm`）；
v ↦ 1（阿基米德位点）。 -/
def weight : IUTIVPlace F → ℝ
  | .finite v => Real.log (v.asIdeal.absNorm : ℝ)
  | .infinite _ => 1

@[simp] theorem weight_finite (v : HeightOneSpectrum (𝓞 F)) :
    weight F (.finite v) = Real.log (v.asIdeal.absNorm : ℝ) := rfl

@[simp] theorem weight_infinite (w : NumberField.InfinitePlace F) :
    weight F (.infinite w) = 1 := rfl

/-- q_v = 剩余域基数：`Ideal.absNorm` 等于商 `𝓞 F ⧸ v` 的基数。
（剩余的域基数是分数域，商在 v 极大时即剩余域本身；此处记录论文所用的基数。） -/
theorem absNorm_eq_cardQuot (v : HeightOneSpectrum (𝓞 F)) :
    v.asIdeal.absNorm = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- 局部次数 [F_v : Q_{vQ}]：有限位点 v 取 e_v·f_v（对 ℤ 的分歧指数乘剩余次数）；
阿基米德位点取 1（实）/2（复）。用于 Def 1.9 (ii) 的 E-度归一化。 -/
def localDegree : IUTIVPlace F → ℕ
  | .finite v => v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ
  | .infinite v => if v.IsComplex then 2 else 1

end IUTIVPlace

/-- R-算术除子组 ADiv_R(F)：V(F) 上的有限 ℝ-线性形式（`Finsupp`）。 -/
abbrev IUTIVArithmeticDivisor : Type _ := IUTIVPlace F →₀ ℝ

namespace IUTIVArithmeticDivisor

/-- deg_F : ADiv_R(F) → ℝ，v ↦ (log q_v | 1) 的线性延拓（Def 1.9 的度映射）。 -/
def degLinearMap : IUTIVArithmeticDivisor F →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (IUTIVPlace.weight F)

/-- Def 1.9 的度映射 deg_F。 -/
abbrev deg (D : IUTIVArithmeticDivisor F) : ℝ := degLinearMap F D

/-- 逐点展开：deg_F(D) = Σ_v c_v · weight(v)。 -/
theorem deg_apply (D : IUTIVArithmeticDivisor F) :
    D.deg = D.sum (fun v c => c * IUTIVPlace.weight F v) := by
  rw [deg, degLinearMap, Finsupp.linearCombination_apply]
  simp only [smul_eq_mul]

@[simp] theorem deg_zero : (0 : IUTIVArithmeticDivisor F).deg = 0 := by
  rw [deg, degLinearMap, map_zero]

@[simp] theorem deg_single (v : IUTIVPlace F) (c : ℝ) :
    degLinearMap F (Finsupp.single v c) = c * IUTIVPlace.weight F v := by
  rw [degLinearMap, Finsupp.linearCombination_single, smul_eq_mul]

/-- Def 1.9 的归一化度 deg(a) = (1/[F:Q]) · deg_F(a)。 -/
def ndegLinearMap : IUTIVArithmeticDivisor F →ₗ[ℝ] ℝ :=
  ((Module.finrank ℚ F : ℝ))⁻¹ • degLinearMap F

/-- Def 1.9 的归一化度。 -/
abbrev ndeg (D : IUTIVArithmeticDivisor F) : ℝ := ndegLinearMap F D

theorem ndeg_apply (D : IUTIVArithmeticDivisor F) :
    D.ndeg = ((Module.finrank ℚ F : ℝ))⁻¹ * D.deg := by
  rw [ndeg, ndegLinearMap, LinearMap.smul_apply, smul_eq_mul]

/-- 支撑 Supp(a)（Def 1.9 (i)）：系数非零的位点集合。 -/
def support (D : IUTIVArithmeticDivisor F) : Set (IUTIVPlace F) := {v | D v ≠ 0}

omit [NumberField F] in
theorem mem_support {D : IUTIVArithmeticDivisor F} {v : IUTIVPlace F} :
    v ∈ D.support ↔ D v ≠ 0 := Iff.rfl

/-- 有效算术除子（Def 1.9 (i)）：所有系数非负。 -/
def IsEffective (D : IUTIVArithmeticDivisor F) : Prop := ∀ v, 0 ≤ D v

/-- Def 1.9 (ii)：支撑在有限位点集 E 上的部分 a_E = Σ_{v∈E} c_v · v。 -/
def part (E : Finset (IUTIVPlace F)) (D : IUTIVArithmeticDivisor F) :
    IUTIVArithmeticDivisor F :=
  ∑ v ∈ E, D v • Finsupp.single v 1

/-- deg_F(a_E) = Σ_{v∈E} c_v · weight(v)。 -/
theorem deg_part (E : Finset (IUTIVPlace F)) (D : IUTIVArithmeticDivisor F) :
    (part F E D).deg = ∑ v ∈ E, D v * IUTIVPlace.weight F v := by
  rw [part, deg, map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_smul, deg_single, smul_eq_mul]
  ring

/-- Def 1.9 (ii) 的 E-度：deg_E(a) = deg(a_E) / Σ_{v∈E} [F_v : Q_{vQ}]（分子为归一化度 ndeg）。
字面拉回等式的精确形式见 `eDegree_pullback_factor`（差因子 [K:F]⁻¹，2026-10-16 落地）；
精确不变式由未归一化分子读数 `eDegreeUnnormalized` 承载（`eDegreeUnnormalized_pullback`）。 -/
def eDegree (E : Finset (IUTIVPlace F)) (D : IUTIVArithmeticDivisor F) : ℝ :=
  (part F E D).ndeg / ∑ v ∈ E, (IUTIVPlace.localDegree F v : ℝ)

/-- Def 1.9 (ii) 的未归一化分子读数：deg_F(a_E) / Σ_{v∈E} [F_v : Q_{vQ}]。
该读数使 (ii)-Thus 的拉回等式精确成立（`eDegreeUnnormalized_pullback`）；
“Thus”字面读数则精确到因子 [K:F]⁻¹（`eDegree_pullback_factor`）。 -/
def eDegreeUnnormalized (E : Finset (IUTIVPlace F)) (D : IUTIVArithmeticDivisor F) : ℝ :=
  (part F E D).deg / ∑ v ∈ E, (IUTIVPlace.localDegree F v : ℝ)

end IUTIVArithmeticDivisor

end PlacesAndWeights

section Pullback

variable {F : Type*} [Field F] [NumberField F]
variable {K : Type*} [Field K] [NumberField K] [Algebra F K]

open IUTIVArithmeticDivisor

/-- w | v 的包装：`v.asIdeal` 上方的素 `Q` 作为 K 的有限位点。 -/
def primeOverPlace {v : HeightOneSpectrum (𝓞 F)}
    (Q : v.asIdeal.primesOver (𝓞 K)) : IUTIVPlace K :=
  .finite ⟨Q.1, Q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.1⟩

/-- 拉回 a|K 在有限位点 v 的纤维部分：Σ_{w | v} c_v · e_w · w（e_w = 分歧指数）。
输出为 K 上的算术除子（用单个位点的 `Finsupp.single` 求和）。 -/
def finiteFiberContribution (v : HeightOneSpectrum (𝓞 F)) :
    IUTIVArithmeticDivisor K := by
  letI : Fintype (v.asIdeal.primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) v.asIdeal).fintype
  exact ∑ Q : v.asIdeal.primesOver (𝓞 K),
    ((Q.1.ramificationIdx (𝓞 F) : ℕ) : ℝ) •
      Finsupp.single (primeOverPlace (F := F) (K := K) Q) 1

/-- 拉回 a|K 在阿基米德位点 v 的纤维部分：Σ_{w | v} e_w · w，e_w = 局部次数
`v.inertiaDeg w`（= [K_w : F_v] ∈ {1,2}）。 -/
def infiniteFiberContribution (v : NumberField.InfinitePlace F) :
    IUTIVArithmeticDivisor K := by
  classical
  exact ∑ w ∈ v.placesOver K,
    ((v.inertiaDeg w : ℕ) : ℝ) • Finsupp.single (.infinite w) 1

/-- 纤维贡献：位点 v ∈ V(F) 的整条纤维（有限/阿基米德分别走对应构造）。 -/
def fiberContribution : IUTIVPlace F → IUTIVArithmeticDivisor K
  | .finite v => finiteFiberContribution v
  | .infinite v => infiniteFiberContribution v

/-- Def 1.9 的拉回 a|K（“evident fashion”的显式约定）：系数 (a|K)_w = c_v · e_w。
见文件头说明：此约定使论文声称的归一化度不变成立。 -/
def pullback (D : IUTIVArithmeticDivisor F) : IUTIVArithmeticDivisor K :=
  D.sum fun v c => c • fiberContribution v

theorem pullback_single (v : IUTIVPlace F) (c : ℝ) :
    pullback (K := K) (Finsupp.single v c) = c • fiberContribution (K := K) v := by
  rw [pullback, Finsupp.sum_single_index (h_zero := by simp)]

theorem pullback_add (D D' : IUTIVArithmeticDivisor F) :
    pullback (F := F) (K := K) (D + D') =
      pullback (F := F) (K := K) D + pullback (F := F) (K := K) D' := by
  rw [pullback, pullback, pullback,
    Finsupp.sum_add_index' (h_zero := fun a => by simp) (h_add := fun a b₁ b₂ => by simp [add_smul])]

/-- 逐纤维：有限位点纤维的度 = (Σ_{w|v} e_w f_w) · log q_v = [K:F] · weight(v)。
机器：q_w = q_v^{f_w}（`Ideal.absNorm_pow_inertiaDeg`），Σ e_w f_w = finrank（`Ideal.sum_ramification_inertia_eq_finrank`），
finrank (𝓞 F) (𝓞 K) = [K:F]（`finrank_ringOfIntegers_eq_fieldDegree`）。 -/
theorem deg_finiteFiberContribution (v : HeightOneSpectrum (𝓞 F)) :
    (finiteFiberContribution (F := F) (K := K) v).deg =
      (Module.finrank F K : ℝ) * IUTIVPlace.weight F (.finite v) := by
  classical
  haveI : v.asIdeal.IsPrime := v.isPrime
  letI : Fintype (v.asIdeal.primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) v.asIdeal).fintype
  have hlog (Q : v.asIdeal.primesOver (𝓞 K)) :
      Real.log (Q.1.absNorm : ℝ) =
        ((Q.1.inertiaDeg (𝓞 F) : ℕ) : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) := by
    have hp : (v.asIdeal.absNorm : ℕ) ^ Q.1.inertiaDeg (𝓞 F) = Q.1.absNorm :=
      Ideal.absNorm_pow_inertiaDeg v.asIdeal Q.1
    have hcast : (Q.1.absNorm : ℝ) =
        (v.asIdeal.absNorm : ℝ) ^ (Q.1.inertiaDeg (𝓞 F)) := by
      rw [← hp, Nat.cast_pow]
    rw [hcast, Real.log_pow]
  rw [finiteFiberContribution, deg, map_sum]
  simp only [map_smul, deg_single, smul_eq_mul, one_mul]
  calc ∑ Q : v.asIdeal.primesOver (𝓞 K),
        ((Q.1.ramificationIdx (𝓞 F) : ℕ) : ℝ) * Real.log (Q.1.absNorm : ℝ)
      = ∑ Q : v.asIdeal.primesOver (𝓞 K),
        ((Q.1.ramificationIdx (𝓞 F) : ℕ) : ℝ) *
          (((Q.1.inertiaDeg (𝓞 F) : ℕ) : ℝ) * Real.log (v.asIdeal.absNorm : ℝ)) := by
        apply Finset.sum_congr rfl
        intro Q _
        rw [hlog Q]
    _ = (∑ Q : v.asIdeal.primesOver (𝓞 K),
          ((Q.1.ramificationIdx (𝓞 F) : ℕ) : ℝ) *
            ((Q.1.inertiaDeg (𝓞 F) : ℕ) : ℝ)) *
          Real.log (v.asIdeal.absNorm : ℝ) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro Q _
        ring
    _ = ((∑ Q : v.asIdeal.primesOver (𝓞 K),
          Q.1.ramificationIdx (𝓞 F) * Q.1.inertiaDeg (𝓞 F) : ℕ) : ℝ) *
          Real.log (v.asIdeal.absNorm : ℝ) := by
        congr 1
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro Q _
        rw [Nat.cast_mul]
    _ = (Module.finrank (𝓞 F) (𝓞 K) : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) := by
        rw [Ideal.sum_ramification_inertia_eq_finrank (R := 𝓞 F) (S := 𝓞 K) v.asIdeal]
    _ = (Module.finrank F K : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) := by
        rw [LeanFormal.IUT.NumberFieldFinitePlace.finrank_ringOfIntegers_eq_fieldDegree (k := F) (K := K)]

/-- 逐纤维：阿基米德纤维的度 = Σ_{w|v} [K_w:F_v] = [K:F] = [K:F]·weight(v)（weight = 1）。
机器：`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`。 -/
theorem deg_infiniteFiberContribution (v : NumberField.InfinitePlace F) :
    (infiniteFiberContribution (F := F) (K := K) v).deg =
      (Module.finrank F K : ℝ) * IUTIVPlace.weight F (.infinite v) := by
  classical
  rw [infiniteFiberContribution, deg, map_sum]
  simp only [map_smul, deg_single, smul_eq_mul, IUTIVPlace.weight_infinite, mul_one]
  rw [← Nat.cast_sum, NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank (K := F) (L := K) v]

/-- 纤维贡献的度：deg_K(fiberContribution v) = [K:F] · weight(v)。 -/
theorem deg_fiberContribution (v : IUTIVPlace F) :
    (fiberContribution (F := F) (K := K) v).deg =
      (Module.finrank F K : ℝ) * IUTIVPlace.weight F v := by
  cases v with
  | finite v => exact deg_finiteFiberContribution v
  | infinite v => exact deg_infiniteFiberContribution v

/-- 纤维贡献的度（`degLinearMap` 形式，供重写；与 `deg_fiberContribution` 定义等价）。 -/
theorem degLinearMap_fiberContribution (v : IUTIVPlace F) :
    degLinearMap K (fiberContribution (F := F) (K := K) v) =
      (Module.finrank F K : ℝ) * IUTIVPlace.weight F v :=
  deg_fiberContribution (F := F) (K := K) v

/-- Def 1.9 拉回的度：deg_K(a|K) = [K:F] · deg_F(a)。 -/
theorem deg_pullback (D : IUTIVArithmeticDivisor F) :
    (pullback (F := F) (K := K) D).deg = (Module.finrank F K : ℝ) * D.deg := by
  refine Finsupp.induction_linear (motive := fun D =>
    degLinearMap K (pullback (F := F) (K := K) D) =
      (Module.finrank F K : ℝ) * degLinearMap F D) D ?_ ?_ ?_
  · simp [pullback]
  · intro D₁ D₂ ih₁ ih₂
    rw [pullback_add, map_add, ih₁, ih₂, map_add]
    ring
  · intro v c
    rw [pullback_single, map_smul, degLinearMap_fiberContribution, deg_single, smul_eq_mul]
    ring

theorem finrank_Q_K_eq_mul (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] :
    ((Module.finrank ℚ K : ℕ) : ℝ) =
      ((Module.finrank ℚ F : ℕ) : ℝ) * ((Module.finrank F K : ℕ) : ℝ) := by
  rw [← Module.finrank_mul_finrank (F := ℚ) (K := F) (A := K), Nat.cast_mul]

/-- Def 1.9 的核心结论：归一化度在拉回下不变，deg(a|K) = deg(a)。
   ⇔ 由 `deg_pullback` 与 [K:Q] = [F:Q]·[K:F]（`Module.finrank_mul_finrank`）直接得到。 -/
theorem ndeg_pullback (D : IUTIVArithmeticDivisor F) :
    (pullback (F := F) (K := K) D).ndeg = D.ndeg := by
  rw [IUTIVArithmeticDivisor.ndeg_apply, IUTIVArithmeticDivisor.ndeg_apply, deg_pullback,
    finrank_Q_K_eq_mul F K]
  have hK : Module.finrank ℚ K ≠ 0 :=
    (Module.finrank_pos_iff_of_free (R := ℚ) (M := K)).mpr inferInstance |>.ne'
  have hFK : ((Module.finrank F K : ℕ) : ℝ) ≠ 0 := by
    have hne : Module.finrank F K ≠ 0 := by
      intro h0
      have h := Module.finrank_mul_finrank (F := ℚ) (K := F) (A := K)
      rw [h0, mul_zero] at h
      exact hK h.symm
    exact Nat.cast_ne_zero.mpr hne
  have hF : ((Module.finrank ℚ F : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      ((Module.finrank_pos_iff_of_free (R := ℚ) (M := F)).mpr inferInstance |>.ne')
  field_simp [hF, hFK]

end Pullback

section FiberNormalizationConstants

/-! ## C2：纤维归一化常数 Σ_{v∈E} [F_v:Q_{vQ}] = [F:Q]（全纤维）与塔式加性

论文：IV Def 1.9 (ii)（L1234–1251）；Explicit estimates Def 1.1 的 [F_v:Q_vQ] 层（L409–427）。
机器：`Ideal.sum_ramification_inertia_eq_finrank`、`NumberField.RingOfIntegers.rank`
（绝对桥 finrank ℤ (𝓞 F) = [F:Q]）、`InfinitePlace.sum_mult_eq`（基 ℚ 只有一个阿基米德位点）。
塔式（C1 所需）：`Ideal.ramificationIdx_tower` + `Ideal.inertiaDeg_tower`。
缩减显式标注：基 ℚ 的有限位点以 `HeightOneSpectrum ℤ` 表示；[F_v:Q_p] 在有限位点按 e_v·f_v
实现（标准局部域事实；与文件既有 deg 机器一致）。 -/

variable {F : Type*} [Field F] [NumberField F]
variable {K : Type*} [Field K] [NumberField K] [Algebra F K]

/-- 塔式 e（基 ℤ）：e(w|ℤ) = e(v|ℤ)·e(w|v)。`Ideal.ramificationIdx_tower` 实例化。 -/
theorem ramificationIdx_tower_base {v : HeightOneSpectrum (𝓞 F)}
    (Q : v.asIdeal.primesOver (𝓞 K)) :
    Q.1.ramificationIdx ℤ = v.asIdeal.ramificationIdx ℤ * Q.1.ramificationIdx (𝓞 F) :=
  Ideal.ramificationIdx_tower (R := ℤ) (S := 𝓞 F) (T := 𝓞 K) (q := v.asIdeal) (r := Q.1)

/-- 塔式 f（基 ℤ）：f(w|ℤ) = f(v|ℤ)·f(w|v)。`Ideal.inertiaDeg_tower` 实例化。 -/
theorem inertiaDeg_tower_base {v : HeightOneSpectrum (𝓞 F)}
    (Q : v.asIdeal.primesOver (𝓞 K)) :
    Q.1.inertiaDeg ℤ = v.asIdeal.inertiaDeg ℤ * Q.1.inertiaDeg (𝓞 F) :=
  Ideal.inertiaDeg_tower (R := ℤ) (S := 𝓞 F) (T := 𝓞 K) (q := v.asIdeal) (r := Q.1)

/-- 有限纤维的局部次数和（塔式 K/F）：Σ_{w|v}[K_w:Q_p] = [K:F]·[F_v:Q_p]（以 e·f 实现）。 -/
theorem sum_localDegree_primesOver (v : HeightOneSpectrum (𝓞 F)) :
    ((∑ Q : v.asIdeal.primesOver (𝓞 K),
        Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ) : ℝ) =
      (Module.finrank F K : ℝ) *
        ((v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ : ℕ) : ℝ) := by
  classical
  haveI : v.asIdeal.IsPrime := v.isPrime
  have hfiber : (∑ Q : v.asIdeal.primesOver (𝓞 K),
        (↑(Q.1.ramificationIdx (𝓞 F)) * ↑(Q.1.inertiaDeg (𝓞 F)) : ℝ)) =
      (Module.finrank F K : ℝ) := by
    rw [← LeanFormal.IUT.NumberFieldFinitePlace.finrank_ringOfIntegers_eq_fieldDegree
        (k := F) (K := K),
      ← Ideal.sum_ramification_inertia_eq_finrank (R := 𝓞 F) (S := 𝓞 K) v.asIdeal,
      Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro Q _
    rw [Nat.cast_mul]
  calc ∑ Q : v.asIdeal.primesOver (𝓞 K),
        (↑(Q.1.ramificationIdx ℤ) * ↑(Q.1.inertiaDeg ℤ) : ℝ)
      = ∑ Q : v.asIdeal.primesOver (𝓞 K),
          ((↑(v.asIdeal.ramificationIdx ℤ) * ↑(v.asIdeal.inertiaDeg ℤ) : ℝ) *
            (↑(Q.1.ramificationIdx (𝓞 F)) * ↑(Q.1.inertiaDeg (𝓞 F)) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro Q _
        rw [ramificationIdx_tower_base Q, inertiaDeg_tower_base Q]
        simp only [Nat.cast_mul]
        ring
      _ = (↑(v.asIdeal.ramificationIdx ℤ) * ↑(v.asIdeal.inertiaDeg ℤ) : ℝ) *
            ∑ Q : v.asIdeal.primesOver (𝓞 K),
              (↑(Q.1.ramificationIdx (𝓞 F)) * ↑(Q.1.inertiaDeg (𝓞 F)) : ℝ) := by
        rw [Finset.mul_sum]
      _ = (↑(v.asIdeal.ramificationIdx ℤ) * ↑(v.asIdeal.inertiaDeg ℤ) : ℝ) *
            (Module.finrank F K : ℝ) := by
        rw [hfiber]
      _ = (Module.finrank F K : ℝ) *
            ((v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
        ring

/-- C2（有限，基 ℚ）：Σ_{v|p} [F_v:Q_p] = [F:Q]。p 以 `HeightOneSpectrum ℤ` 表示。 -/
theorem sum_localDegree_finiteFiber_base (p : HeightOneSpectrum ℤ) :
    ((∑ Q : p.asIdeal.primesOver (𝓞 F),
        Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ) : ℝ) =
      (Module.finrank ℚ F : ℝ) := by
  classical
  haveI : p.asIdeal.IsPrime := p.isPrime
  rw [← NumberField.RingOfIntegers.rank,
    ← Ideal.sum_ramification_inertia_eq_finrank (R := ℤ) (S := 𝓞 F) p.asIdeal,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro Q _
  rw [Nat.cast_mul]

/-- 局部次数（阿基米德位点）= `NumberField.InfinitePlace.mult`（实 1 / 复 2）。 -/
theorem localDegree_infinite_eq_mult (w : NumberField.InfinitePlace F) :
    IUTIVPlace.localDegree F (.infinite w) = NumberField.InfinitePlace.mult w := by
  simp only [IUTIVPlace.localDegree, NumberField.InfinitePlace.mult]
  by_cases hw : w.IsComplex
  · rw [if_pos hw, if_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)]
  · rw [if_neg hw, if_pos (NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hw)]

/-- C2（阿基米德，基 ℚ）：Σ_{w|∞} [F_w:R] = [F:Q]（ℚ 只有一个阿基米德位点，即全体）。 -/
theorem sum_localDegree_infinitePlaces_base :
    ((∑ w : NumberField.InfinitePlace F, IUTIVPlace.localDegree F (.infinite w)) : ℝ) =
      (Module.finrank ℚ F : ℝ) := by
  simp only [localDegree_infinite_eq_mult]
  rw [← Nat.cast_sum, NumberField.InfinitePlace.sum_mult_eq]

end FiberNormalizationConstants

section FiberInclusion

/-! ## C1 前置：位点纤维、支撑与 part 的 filter 表示

论文：IV Def 1.9 (ii)（正文 L1234–1251）中的 E|K = “E 之上的位点集”。
本段给出该纤维的显式构造 `fiberOf`、纤维唯一性、纤维贡献在纤维外的零系数，
以及 `part`（a_E）的 `Finsupp.filter` 表示（逐点值）。拉回恒等式与 E-度
不变性见下一段；本段结论是纯组合事实，不含拉回约定。

缩减显式标注：
- `IUTIVPlace` 的 `DecidableEq` 由经典选择给出（非计算性），仅用于 Finset 组合；
- 有限位点纤维取 `Ideal.primesOver`（Fintype 来自 `Algebra.QuasiFinite`），
  阿基米德位点纤维取 `InfinitePlace.placesOver`，两者均为 Mathlib 的“v 之上”位点集。 -/

variable {F : Type*} [Field F] [NumberField F]
variable {K : Type*} [Field K] [NumberField K] [Algebra F K]

open IUTIVArithmeticDivisor

/-- `IUTIVPlace F` 的经典 `DecidableEq`（非计算性；Finset 组合所需）。 -/
noncomputable instance IUTIVPlace.instDecidableEq : DecidableEq (IUTIVPlace F) :=
  Classical.decEq _

/-- 有限位点 v 之上的 K-位点纤维：`v.asIdeal` 上方素理想对应的 K-位点。 -/
def finiteFiberOf (v : HeightOneSpectrum (𝓞 F)) : Finset (IUTIVPlace K) := by
  letI : Fintype (v.asIdeal.primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) v.asIdeal).fintype
  exact (Finset.univ : Finset (v.asIdeal.primesOver (𝓞 K))).image fun Q =>
    primeOverPlace (F := F) (K := K) Q

/-- 阿基米德位点 v 之上的 K-位点纤维。 -/
def infiniteFiberOf (v : NumberField.InfinitePlace F) : Finset (IUTIVPlace K) :=
  (v.placesOver K).toFinset.image fun w => (IUTIVPlace.infinite w : IUTIVPlace K)

/-- 位点纤维：v ↦ {w | w 在 v 之上}（Def 1.9 (ii) 中 E|K 的逐点形式）。 -/
def fiberOf : IUTIVPlace F → Finset (IUTIVPlace K)
  | .finite v => finiteFiberOf (F := F) (K := K) v
  | .infinite v => infiniteFiberOf (F := F) (K := K) v

theorem mem_finiteFiberOf {v : HeightOneSpectrum (𝓞 F)} {w : IUTIVPlace K} :
    w ∈ finiteFiberOf (F := F) (K := K) v ↔
      ∃ Q : v.asIdeal.primesOver (𝓞 K), primeOverPlace (F := F) (K := K) Q = w := by
  unfold finiteFiberOf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨Q, -, hQ⟩
    exact ⟨Q, hQ⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, Finset.mem_univ Q, hQ⟩

theorem mem_infiniteFiberOf {v : NumberField.InfinitePlace F} {w : IUTIVPlace K} :
    w ∈ infiniteFiberOf (F := F) (K := K) v ↔
      ∃ w' ∈ v.placesOver K, (IUTIVPlace.infinite w' : IUTIVPlace K) = w := by
  unfold infiniteFiberOf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w', hw', hw⟩
    exact ⟨w', (Set.mem_toFinset).mp hw', hw⟩
  · rintro ⟨w', hw', hw⟩
    exact ⟨w', (Set.mem_toFinset).mpr hw', hw⟩

theorem mem_fiberOf_finite {v : HeightOneSpectrum (𝓞 F)} {w : IUTIVPlace K} :
    w ∈ fiberOf (F := F) (K := K) (.finite v) ↔
      ∃ Q : v.asIdeal.primesOver (𝓞 K), primeOverPlace (F := F) (K := K) Q = w :=
  mem_finiteFiberOf

theorem mem_fiberOf_infinite {v : NumberField.InfinitePlace F} {w : IUTIVPlace K} :
    w ∈ fiberOf (F := F) (K := K) (.infinite v) ↔
      ∃ w' ∈ v.placesOver K, (IUTIVPlace.infinite w' : IUTIVPlace K) = w :=
  mem_infiniteFiberOf

/-- 纤维唯一性：一个 K-位点至多位于一个 F-位点之上。 -/
theorem fiberOf_unique {v v' : IUTIVPlace F} {w : IUTIVPlace K}
    (hv : w ∈ fiberOf (F := F) (K := K) v)
    (hv' : w ∈ fiberOf (F := F) (K := K) v') : v = v' := by
  cases v with
  | finite v =>
    rw [mem_fiberOf_finite] at hv
    cases v' with
    | finite v' =>
      rw [mem_fiberOf_finite] at hv'
      obtain ⟨Q, hQ⟩ := hv
      obtain ⟨Q', hQ'⟩ := hv'
      have hsingle := IUTIVPlace.finite.inj (hQ'.trans hQ.symm)
      have hQ1 : Q'.1 = Q.1 :=
        congrArg (fun s : HeightOneSpectrum (𝓞 K) => s.asIdeal) hsingle
      have h1 : v.asIdeal = Ideal.under (𝓞 F) Q.1 := Q.2.2.over
      have h2 : v'.asIdeal = Ideal.under (𝓞 F) Q.1 := by
        have hlies : Q'.1.LiesOver v'.asIdeal := Q'.2.2
        rw [hQ1] at hlies
        exact hlies.over
      exact congrArg IUTIVPlace.finite (HeightOneSpectrum.ext (h1.trans h2.symm))
    | infinite v' =>
      rw [mem_fiberOf_infinite] at hv'
      obtain ⟨Q, hQ⟩ := hv
      obtain ⟨w', -, hw'⟩ := hv'
      have hbad : primeOverPlace (F := F) (K := K) Q = IUTIVPlace.infinite w' :=
        hQ.trans hw'.symm
      cases hbad
  | infinite v =>
    rw [mem_fiberOf_infinite] at hv
    cases v' with
    | finite v' =>
      rw [mem_fiberOf_finite] at hv'
      obtain ⟨w', -, hw'⟩ := hv
      obtain ⟨Q', hQ'⟩ := hv'
      have hbad : (IUTIVPlace.infinite w' : IUTIVPlace K) = primeOverPlace (F := F) (K := K) Q' :=
        hw'.trans hQ'.symm
      cases hbad
    | infinite v' =>
      rw [mem_fiberOf_infinite] at hv'
      obtain ⟨w₁, hw₁, he₁⟩ := hv
      obtain ⟨w₂, hw₂, he₂⟩ := hv'
      have hw : w₁ = w₂ := IUTIVPlace.infinite.inj (he₁.trans he₂.symm)
      subst hw
      have hl₁ : w₁.1.LiesOver v.1 := by
        simpa only [NumberField.InfinitePlace.placesOver, Set.mem_setOf_eq] using hw₁
      have hl₂ : w₁.1.LiesOver v'.1 := by
        simpa only [NumberField.InfinitePlace.placesOver, Set.mem_setOf_eq] using hw₂
      exact congrArg IUTIVPlace.infinite (Subtype.ext (hl₁.comp_eq.symm.trans hl₂.comp_eq))

/-- 有限位点纤维贡献在纤维外的系数为零。 -/
theorem finiteFiberContribution_apply_eq_zero {v : HeightOneSpectrum (𝓞 F)} {w : IUTIVPlace K}
    (hw : w ∉ finiteFiberOf (F := F) (K := K) v) :
    finiteFiberContribution (F := F) (K := K) v w = 0 := by
  have hterm (Q : v.asIdeal.primesOver (𝓞 K)) :
      (((Q.1.ramificationIdx (𝓞 F) : ℕ) : ℝ) •
        Finsupp.single (primeOverPlace (F := F) (K := K) Q) (1 : ℝ)) w = 0 := by
    have hne : primeOverPlace (F := F) (K := K) Q ≠ w := fun h =>
      hw ((mem_finiteFiberOf (F := F) (K := K)).mpr ⟨Q, h⟩)
    rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, if_neg hne, mul_zero]
  simp only [finiteFiberContribution, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun Q _ => hterm Q

/-- 阿基米德位点纤维贡献在纤维外的系数为零。 -/
theorem infiniteFiberContribution_apply_eq_zero {v : NumberField.InfinitePlace F} {w : IUTIVPlace K}
    (hw : w ∉ infiniteFiberOf (F := F) (K := K) v) :
    infiniteFiberContribution (F := F) (K := K) v w = 0 := by
  have hterm (w' : NumberField.InfinitePlace K) (hw' : w' ∈ v.placesOver K) :
      (((v.inertiaDeg w' : ℕ) : ℝ) • Finsupp.single (IUTIVPlace.infinite w') (1 : ℝ)) w = 0 := by
    have hne : (IUTIVPlace.infinite w' : IUTIVPlace K) ≠ w := fun h =>
      hw ((mem_infiniteFiberOf (F := F) (K := K)).mpr ⟨w', hw', h⟩)
    rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, if_neg hne, mul_zero]
  simp only [infiniteFiberContribution, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  exact hterm w' ((Set.mem_toFinset).mp hw')

/-- 纤维贡献在纤维外的系数为零（统一形式）。 -/
theorem fiberContribution_apply_eq_zero {v : IUTIVPlace F} {w : IUTIVPlace K}
    (hw : w ∉ fiberOf (F := F) (K := K) v) :
    fiberContribution (F := F) (K := K) v w = 0 := by
  cases v with
  | finite v => exact finiteFiberContribution_apply_eq_zero hw
  | infinite v => exact infiniteFiberContribution_apply_eq_zero hw

/-- `part`（Def 1.9 (ii) 的 a_E）即 `Finsupp.filter`：E 内保留原系数，E 外归零。 -/
theorem part_eq_filter (E : Finset (IUTIVPlace F)) (D : IUTIVArithmeticDivisor F) :
    part F E D = D.filter (fun w => w ∈ E) := by
  ext w
  rw [part, Finsupp.finsetSum_apply, Finsupp.filter_apply]
  trans ∑ v ∈ E, (if v = w then D v else 0)
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases h : v = w
    · simp only [if_pos h, mul_one]
    · simp only [if_neg h, mul_zero]
  · exact Finset.sum_ite_eq' E w D

/-- `part` 的逐点值：w ∈ E 时取原系数，否则取 0。 -/
theorem part_apply (E : Finset (IUTIVPlace F)) (D : IUTIVArithmeticDivisor F) (w : IUTIVPlace F) :
    part F E D w = if w ∈ E then D w else 0 := by
  rw [part_eq_filter, Finsupp.filter_apply]

/-- `part` 的支撑包含于 E。 -/
theorem part_support_subset {E : Finset (IUTIVPlace F)} {D : IUTIVArithmeticDivisor F}
    {w : IUTIVPlace F} (hw : w ∈ (part F E D).support) : w ∈ E := by
  by_contra hwE
  have h0 : part F E D w = 0 := by rw [part_apply, if_neg hwE]
  exact hw h0

theorem part_smul (E : Finset (IUTIVPlace F)) (c : ℝ) (D : IUTIVArithmeticDivisor F) :
    part F E (c • D) = c • part F E D := by
  rw [part_eq_filter, part_eq_filter, Finsupp.filter_smul]

theorem part_add (E : Finset (IUTIVPlace F)) (D D' : IUTIVArithmeticDivisor F) :
    part F E (D + D') = part F E D + part F E D' := by
  rw [part_eq_filter, part_eq_filter, part_eq_filter]
  exact map_add (Finsupp.filterAddHom (fun w : IUTIVPlace F => w ∈ E)) D D'

/-- 支撑包含于 E 的除子：a_E = a。 -/
theorem part_eq_self_of_support_subset (E : Finset (IUTIVPlace F)) (D : IUTIVArithmeticDivisor F)
    (h : ∀ w, D w ≠ 0 → w ∈ E) : part F E D = D := by
  rw [part_eq_filter]
  exact (Finsupp.filter_eq_self_iff (fun w : IUTIVPlace F => w ∈ E) D).mpr h

end FiberInclusion

section FiberDegreeLedger

/-! ## C1：Def 1.9 (ii) 的 E-度与纤维拉回（2026-10-16 落地）

论文：IV Def 1.9 (ii)（正文 L1204–1254；PDF 物理页 21）：E ⊆ V(F) 为某 vQ ∈ V(Q) 之上的纤维，
a_E = Σ_{v∈E} c_v·v，deg_E(a) = deg(a_E)/Σ_{v∈E}[F_v:Q_vQ]，以及
“Thus, for any finite extension K of F, we have deg_{E|K}(a|K) = deg_E(a)”，
其中 E|K ⊆ V(K) 为 E 之上的位点集。

本段在拉回约定 λ_w = e_w（同 `Pullback` 段）下精确化该断言：
- 精确不变式落在未归一化分子读数 `eDegreeUnnormalized`（分子 deg_F(a_E)）：
  `eDegreeUnnormalized_pullback`（“Thus”的成立读数）。
- 字面（归一化分子）读数满足因子律 `eDegree_pullback_factor`：
  eDegree_{E|K}(a|K) = eDegree_E(a)/[K:F]（[K:F] 偏离为精确负结果；
  两独立算例见 2026-10-16 侦察笔记 `estimates-cards-notes.md`）。

推导链全在本段：纤维不交 → 逐纤维局部次数和（有限：`Finset.sum_of_injOn` +
`sum_localDegree_primesOver`；阿基米德：`infinitePlace_mult_eq_inertiaDeg_mul` +
`sum_inertiaDeg_eq_finrank`）→ `sum_localDegree_biUnion` → `part_pullback`
（`Finsupp.induction_linear` + 纤维不交）→ `deg_part_pullback` → 两读数。

缩减显式标注：`IUTIVPlace` 的 DecidableEq 为经典非计算性；论文的 E 为 ℚ-位点纤维，
此处对任意有限 E 证明（更强，无额外假设）；阿基米德纤维经 `InfinitePlace.placesOver` 的 toFinset。 -/

variable {F : Type*} [Field F] [NumberField F]
variable {K : Type*} [Field K] [NumberField K] [Algebra F K]

open IUTIVArithmeticDivisor

theorem finrank_QF_cast_ne_zero : ((Module.finrank ℚ F : ℕ) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr
    ((Module.finrank_pos_iff_of_free (R := ℚ) (M := F)).mpr inferInstance |>.ne')

theorem finrank_FK_cast_ne_zero : ((Module.finrank F K : ℕ) : ℝ) ≠ 0 := by
  have hK : Module.finrank ℚ K ≠ 0 :=
    (Module.finrank_pos_iff_of_free (R := ℚ) (M := K)).mpr inferInstance |>.ne'
  have hne : Module.finrank F K ≠ 0 := by
    intro h0
    have h := Module.finrank_mul_finrank (F := ℚ) (K := F) (A := K)
    rw [h0, mul_zero] at h
    exact hK h.symm
  exact Nat.cast_ne_zero.mpr hne

/-- K-位点纤维两两不交：一个 K-位点至多位于一个 F-位点之上。 -/
theorem fiberOf_disjoint {v v' : IUTIVPlace F} (h : v ≠ v') :
    Disjoint (fiberOf (F := F) (K := K) v) (fiberOf (F := F) (K := K) v') := by
  rw [Finset.disjoint_left]
  intro w hw hw'
  exact h (fiberOf_unique hw hw')

/-- `Finset.sum_biUnion` 所需的两两不交条件（E 之上纤维族）。 -/
theorem fiberOf_pairwiseDisjoint (E : Finset (IUTIVPlace F)) :
    Set.PairwiseDisjoint (↑E : Set (IUTIVPlace F)) (fiberOf (F := F) (K := K)) := by
  intro v _ v' _ hne
  exact fiberOf_disjoint hne

/-- 有限位点纤维的局部次数和：Σ_{w|v} [K_w:Q_p] = [K:F]·[F_v:Q_p]（e·f 记账）。
机器：`Finset.sum_of_injOn`（primesOver → fiberOf 的双射计数）+ `sum_localDegree_primesOver`。 -/
theorem sum_localDegree_finiteFiberOf (v : HeightOneSpectrum (𝓞 F)) :
    (∑ w ∈ finiteFiberOf (F := F) (K := K) v, (IUTIVPlace.localDegree K w : ℝ)) =
      (Module.finrank F K : ℝ) * (IUTIVPlace.localDegree F (.finite v) : ℝ) := by
  classical
  have hbij : (∑ Q : v.asIdeal.primesOver (𝓞 K),
        (IUTIVPlace.localDegree K (primeOverPlace (F := F) (K := K) Q) : ℝ)) =
      ∑ w ∈ finiteFiberOf (F := F) (K := K) v, (IUTIVPlace.localDegree K w : ℝ) :=
    Finset.sum_of_injOn
      (s := (Finset.univ : Finset (v.asIdeal.primesOver (𝓞 K))))
      (t := finiteFiberOf (F := F) (K := K) v)
      (f := fun Q : v.asIdeal.primesOver (𝓞 K) =>
        (IUTIVPlace.localDegree K (primeOverPlace (F := F) (K := K) Q) : ℝ))
      (g := fun w : IUTIVPlace K => (IUTIVPlace.localDegree K w : ℝ))
      (fun Q : v.asIdeal.primesOver (𝓞 K) => primeOverPlace (F := F) (K := K) Q)
      (fun Q _ Q' _ h => Subtype.ext (congrArg HeightOneSpectrum.asIdeal (IUTIVPlace.finite.inj h)))
      (fun Q _ => (mem_finiteFiberOf (F := F) (K := K)).mpr ⟨Q, rfl⟩)
      (fun w hw hnot => by
        obtain ⟨Q, hQ⟩ := (mem_finiteFiberOf (F := F) (K := K)).mp hw
        exact absurd ⟨Q, Finset.mem_univ Q, hQ⟩ hnot)
      (fun Q _ => rfl)
  rw [← hbij]
  rw [show (∑ Q : v.asIdeal.primesOver (𝓞 K),
        (IUTIVPlace.localDegree K (primeOverPlace (F := F) (K := K) Q) : ℝ)) =
      ∑ Q : v.asIdeal.primesOver (𝓞 K),
        ((Q.1.ramificationIdx ℤ) : ℝ) * ((Q.1.inertiaDeg ℤ) : ℝ) from
    Finset.sum_congr rfl fun Q _ => by
      rw [show IUTIVPlace.localDegree K (primeOverPlace (F := F) (K := K) Q) =
          Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ from rfl, Nat.cast_mul]]
  exact sum_localDegree_primesOver (F := F) (K := K) v

/-- 阿基米德局部次数的加权恒等式：mult(w) = [K_w:F_v]·mult(v)（w 在 v 之上）。
分情形：分歧（w 复/v 实，inertiaDeg=2）与不分歧（inertiaDeg=1，mult 相等）。 -/
theorem infinitePlace_mult_eq_inertiaDeg_mul {v : NumberField.InfinitePlace F}
    {w : NumberField.InfinitePlace K} (hl : w.1.LiesOver v.1) :
    NumberField.InfinitePlace.mult w =
      v.inertiaDeg w * NumberField.InfinitePlace.mult v := by
  classical
  haveI : w.1.LiesOver v.1 := hl
  by_cases hram : w.IsRamified F
  · rw [NumberField.InfinitePlace.inertiaDeg_eq_two (K := F) (L := K) (v := v) (w := w)
      ⟨hl, hram⟩]
    have hw2 : NumberField.InfinitePlace.mult w = 2 :=
      NumberField.InfinitePlace.mult_isComplex ⟨w, hram.isComplex⟩
    have hv1 : NumberField.InfinitePlace.mult v = 1 := by
      refine NumberField.InfinitePlace.mult_isReal ⟨v, ?_⟩
      have h := hram.isReal
      rwa [NumberField.InfinitePlace.LiesOver.comap_eq w v] at h
    rw [hw2, hv1, mul_one]
  · have hunram : w.IsUnramified F := not_not.mp hram
    rw [NumberField.InfinitePlace.inertiaDeg_eq_one (K := F) (L := K) (v := v) (w := w)
      ⟨hl, hunram⟩, one_mul]
    rw [← hunram.eq, NumberField.InfinitePlace.LiesOver.comap_eq w v]

/-- v 之上阿基米德位点的 mult 和：Σ_{w|v} mult(w) = [K:F]·mult(v)（ℕ 层）。 -/
theorem sum_mult_placesOver_toFinset (v : NumberField.InfinitePlace F) :
    (∑ w ∈ (v.placesOver K).toFinset, NumberField.InfinitePlace.mult w) =
      Module.finrank F K * NumberField.InfinitePlace.mult v := by
  classical
  calc ∑ w ∈ (v.placesOver K).toFinset, NumberField.InfinitePlace.mult w
      = ∑ w ∈ (v.placesOver K).toFinset,
          v.inertiaDeg w * NumberField.InfinitePlace.mult v := by
        apply Finset.sum_congr rfl
        intro w hw
        exact infinitePlace_mult_eq_inertiaDeg_mul (F := F) (K := K) (v := v) (w := w)
          ((Set.mem_toFinset (s := v.placesOver K)).mp hw)
    _ = (∑ w ∈ (v.placesOver K).toFinset, v.inertiaDeg w) *
          NumberField.InfinitePlace.mult v := by
        rw [Finset.sum_mul]
    _ = Module.finrank F K * NumberField.InfinitePlace.mult v := by
        rw [← NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank (K := F) (L := K) v]

/-- 阿基米德位点纤维的局部次数和：Σ_{w|v} [K_w:F_v] = [K:F]（weight(v)=1）。 -/
theorem sum_localDegree_infiniteFiberOf (v : NumberField.InfinitePlace F) :
    (∑ w ∈ infiniteFiberOf (F := F) (K := K) v, (IUTIVPlace.localDegree K w : ℝ)) =
      (Module.finrank F K : ℝ) * (IUTIVPlace.localDegree F (.infinite v) : ℝ) := by
  classical
  have hsum : (∑ w ∈ infiniteFiberOf (F := F) (K := K) v,
        (IUTIVPlace.localDegree K w : ℝ)) =
      ((∑ w ∈ (v.placesOver K).toFinset, NumberField.InfinitePlace.mult w) : ℝ) := by
    unfold infiniteFiberOf
    rw [Finset.sum_image
      (f := fun w : IUTIVPlace K => (IUTIVPlace.localDegree K w : ℝ))
      (g := fun w : NumberField.InfinitePlace K => (IUTIVPlace.infinite w : IUTIVPlace K))
      (fun w _ w' _ h => IUTIVPlace.infinite.inj h)]
    apply Finset.sum_congr rfl
    intro w _
    exact congrArg Nat.cast (localDegree_infinite_eq_mult (F := K) w)
  rw [hsum, ← Nat.cast_sum, sum_mult_placesOver_toFinset, Nat.cast_mul,
    localDegree_infinite_eq_mult]

/-- 逐位点纤维的局部次数和：任意 v ∈ V(F)，Σ_{w|v} ld(w) = [K:F]·ld(v)。 -/
theorem sum_localDegree_fiberOf (v : IUTIVPlace F) :
    (∑ w ∈ fiberOf (F := F) (K := K) v, (IUTIVPlace.localDegree K w : ℝ)) =
      (Module.finrank F K : ℝ) * (IUTIVPlace.localDegree F v : ℝ) := by
  cases v with
  | finite v => exact sum_localDegree_finiteFiberOf (F := F) (K := K) v
  | infinite v => exact sum_localDegree_infiniteFiberOf (F := F) (K := K) v

/-- E 之上纤维的局部次数乘性：Σ_{w∈E|K} ld(w) = [K:F]·Σ_{v∈E} ld(v)。 -/
theorem sum_localDegree_biUnion (E : Finset (IUTIVPlace F)) :
    (∑ w ∈ E.biUnion (fiberOf (F := F) (K := K)), (IUTIVPlace.localDegree K w : ℝ)) =
      (Module.finrank F K : ℝ) * ∑ v ∈ E, (IUTIVPlace.localDegree F v : ℝ) := by
  classical
  rw [Finset.sum_biUnion (fiberOf_pairwiseDisjoint (F := F) (K := K) E), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact sum_localDegree_fiberOf (F := F) (K := K) v

/-- part 与拉回交换：a_{E|K}|K = (a_E)|K（E|K = E 之上的 K-位点集）。
证明：`Finsupp.induction_linear` 归约到单点，单点情形用纤维不交与纤维贡献的零系数。 -/
theorem part_pullback (E : Finset (IUTIVPlace F)) (D : IUTIVArithmeticDivisor F) :
    part K (E.biUnion (fiberOf (F := F) (K := K))) (pullback (F := F) (K := K) D) =
      pullback (F := F) (K := K) (part F E D) := by
  refine Finsupp.induction_linear (motive := fun D =>
    part K (E.biUnion (fiberOf (F := F) (K := K))) (pullback (F := F) (K := K) D) =
      pullback (F := F) (K := K) (part F E D)) D ?_ ?_ ?_
  · simp [pullback, part]
  · intro D₁ D₂ ih₁ ih₂
    rw [pullback_add, part_add (F := K), ih₁, ih₂, part_add (F := F), pullback_add]
  · intro v c
    by_cases hv : v ∈ E
    · have hpart : part F E (Finsupp.single v c) = Finsupp.single v c :=
        part_eq_self_of_support_subset E (Finsupp.single v c) fun w hw => by
          rw [Finsupp.single_apply_ne_zero] at hw
          exact hw.1.symm ▸ hv
      have hsupp : ∀ w : IUTIVPlace K, fiberContribution (F := F) (K := K) v w ≠ 0 →
          w ∈ E.biUnion (fiberOf (F := F) (K := K)) := fun w hw => by
        by_contra hwE
        have hnf : w ∉ fiberOf (F := F) (K := K) v := fun hwf =>
          hwE (Finset.mem_biUnion.mpr ⟨v, hv, hwf⟩)
        exact hw (fiberContribution_apply_eq_zero hnf)
      rw [pullback_single (F := F) (K := K) v c, part_smul (F := K), hpart,
        pullback_single (F := F) (K := K) v c,
        part_eq_self_of_support_subset (E.biUnion (fiberOf (F := F) (K := K)))
          (fiberContribution (F := F) (K := K) v) hsupp]
    · have hpart : part F E (Finsupp.single v c) = 0 := by
        ext w
        rw [part_apply (F := F), Finsupp.zero_apply]
        by_cases hw : w ∈ E
        · rw [if_pos hw, Finsupp.single_apply]
          exact if_neg (fun hwv : v = w => hv (hwv.symm ▸ hw))
        · rw [if_neg hw]
      have hzero : part K (E.biUnion (fiberOf (F := F) (K := K)))
          (fiberContribution (F := F) (K := K) v) = 0 := by
        ext w
        rw [part_apply (F := K), Finsupp.zero_apply]
        by_cases hwE : w ∈ E.biUnion (fiberOf (F := F) (K := K))
        · rw [if_pos hwE]
          obtain ⟨v', hv'E, hwv'⟩ := Finset.mem_biUnion.mp hwE
          have hnf : w ∉ fiberOf (F := F) (K := K) v := fun hwf =>
            hv ((fiberOf_unique hwf hwv').symm ▸ hv'E)
          exact fiberContribution_apply_eq_zero hnf
        · rw [if_neg hwE]
      rw [pullback_single (F := F) (K := K) v c, part_smul (F := K), hpart, hzero,
        smul_zero]
      simp [pullback]

/-- deg(part)：deg_K(a_{E|K}|K) = [K:F]·deg_F(a_E)（part 交换 + `deg_pullback`）。 -/
theorem deg_part_pullback (E : Finset (IUTIVPlace F)) (D : IUTIVArithmeticDivisor F) :
    (part K (E.biUnion (fiberOf (F := F) (K := K))) (pullback (F := F) (K := K) D)).deg =
      (Module.finrank F K : ℝ) * (part F E D).deg := by
  rw [part_pullback, deg_pullback]

/-- Def 1.9 (ii) 的精确拉回不变（未归一化分子读数）：
eDegreeUnnormalized_{E|K}(a|K) = eDegreeUnnormalized_E(a)（“Thus”的成立读数）。 -/
theorem eDegreeUnnormalized_pullback (E : Finset (IUTIVPlace F))
    (D : IUTIVArithmeticDivisor F) :
    eDegreeUnnormalized K (E.biUnion (fiberOf (F := F) (K := K)))
        (pullback (F := F) (K := K) D) =
      eDegreeUnnormalized F E D := by
  unfold eDegreeUnnormalized
  rw [deg_part_pullback, sum_localDegree_biUnion]
  exact mul_div_mul_left _ _ finrank_FK_cast_ne_zero

/-- 两读数关系：eDegree = (1/[F:Q])·eDegreeUnnormalized（定义层恒等式）。 -/
theorem eDegree_eq_inv_finrank_mul_eDegreeUnnormalized (E : Finset (IUTIVPlace F))
    (D : IUTIVArithmeticDivisor F) :
    eDegree F E D = ((Module.finrank ℚ F : ℕ) : ℝ)⁻¹ * eDegreeUnnormalized F E D := by
  unfold eDegree eDegreeUnnormalized
  rw [IUTIVArithmeticDivisor.ndeg_apply]
  ring

/-- Def 1.9 (ii) “Thus”的字面读数（归一化分子）：eDegree_{E|K}(a|K) = eDegree_E(a)/[K:F]。
   与字面等式 deg_{E|K}(a|K) = deg_E(a) 相差 [K:F] 因子（精确负结果；
   两独立算例见 2026-10-16 侦察笔记）。 -/
theorem eDegree_pullback_factor (E : Finset (IUTIVPlace F))
    (D : IUTIVArithmeticDivisor F) :
    eDegree K (E.biUnion (fiberOf (F := F) (K := K))) (pullback (F := F) (K := K) D) =
      eDegree F E D / (Module.finrank F K : ℝ) := by
  rw [eDegree_eq_inv_finrank_mul_eDegreeUnnormalized
        (E.biUnion (fiberOf (F := F) (K := K))) (pullback (F := F) (K := K) D),
    eDegreeUnnormalized_pullback, eDegree_eq_inv_finrank_mul_eDegreeUnnormalized E D,
    finrank_Q_K_eq_mul F K]
  field_simp [finrank_QF_cast_ne_zero, finrank_FK_cast_ne_zero,
    mul_ne_zero finrank_QF_cast_ne_zero finrank_FK_cast_ne_zero]

end FiberDegreeLedger

section ExplicitLeaves

/-! ## Explicit estimates 叶引理（承接报告 §4.3 与任务包①的小额项） -/

/-- Explicit estimates, Lemma 1.11（L897）：0 ≤ a − log a − 1（a > 0）。
论文："well-known and entirely elementary"。 -/
theorem iutExplicitLemma111_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ a - Real.log a - 1 := by
  linarith [Real.log_le_sub_one_of_pos ha]

/-- Explicit estimates, Lemma 1.11 推论（L~903）：log(1+x) − a·x ≤ a − log a − 1（a > 0，x ≥ 0）。
论文：取 "a" 为 a·(1+x)。 -/
theorem iutExplicitLemma111_linearization (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) :
    Real.log (1 + x) - a * x ≤ a - Real.log a - 1 := by
  have h1x : 0 < 1 + x := by linarith
  have hpos : 0 < a * (1 + x) := mul_pos ha h1x
  have h := iutExplicitLemma111_nonneg (a * (1 + x)) hpos
  rw [Real.log_mul ha.ne' h1x.ne'] at h
  linarith

/-! ## Explicit estimates, Lemma 1.3（L486）代数内核

缩减显式标注：论文的 h□、h^tor_□ 是 V(F)_non/V(F)_arc 上的加权和（权重 1 与 1/[F:Q] 归一化）。
以下给出其**逐点事实与加权和内核对**（论文证明对这些事实逐项求和）。原登记（2026-10-16 上午）：
“完整 h□-层陈述需要 V(F) 绝对值层（|·|_v 与 1/[F:Q]），未在本文件落地，属已登记卡”。
2026-10-16 晚更新（取代该卡）：h□ 高度层已落地，见下方 `section HeightBoxLayer`
（absValAt、支撑有限集、h_non/h_arc/h^tor 层、Lemma 1.3 (i)/(iv)）。 -/

/-- Lemma 1.3 证明中的第一个“易验证”事实（L~512）：max{s, s⁻¹} = max{s,1}·max{s⁻¹,1}（s > 0）。 -/
theorem max_self_inv_eq_max_mul_max (s : ℝ) (hs : 0 < s) :
    max s s⁻¹ = max s 1 * max s⁻¹ 1 := by
  rcases le_total 1 s with h | h
  · have h2 : s⁻¹ ≤ 1 := by
      simpa [mul_one, inv_mul_cancel₀ hs.ne'] using
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs.le)
    rw [max_eq_left (le_trans h2 h), max_eq_left h, max_eq_right h2, mul_one]
  · have h2 : 1 ≤ s⁻¹ := by
      simpa [mul_one, inv_mul_cancel₀ hs.ne'] using
        mul_le_mul_of_nonneg_left h (inv_pos.mpr hs).le
    rw [max_eq_right (le_trans h h2), max_eq_right h, max_eq_left h2, one_mul]

/-- Lemma 1.3 (i) 第二等式（逐点）：log max{s,s⁻¹} = log max{s,1} + log max{s⁻¹,1}。 -/
theorem log_max_self_inv_eq (s : ℝ) (hs : 0 < s) :
    Real.log (max s s⁻¹) = Real.log (max s 1) + Real.log (max s⁻¹ 1) := by
  rw [max_self_inv_eq_max_mul_max s hs, Real.log_mul]
  · exact (lt_max_iff.mpr (Or.inl hs)).ne'
  · exact (lt_max_iff.mpr (Or.inl (inv_pos.mpr hs))).ne'

/-- Lemma 1.3 证明中的第二个“易验证”事实（L~555）：max{st,1} ≤ max{s,1}·max{t,1}（s,t ≥ 0）。 -/
theorem max_mul_one_le_max_mul_max (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    max (s * t) 1 ≤ max s 1 * max t 1 := by
  rcases le_total 1 s with h₁ | h₁ <;> rcases le_total 1 t with h₂ | h₂
  · have hst : 1 ≤ s * t := by
      simpa using mul_le_mul h₁ h₂ zero_le_one hs
    have heq : max (s * t) 1 = max s 1 * max t 1 := by
      rw [max_eq_left hst, max_eq_left h₁, max_eq_left h₂]
    exact heq.le
  · rw [max_eq_left h₁, max_eq_right h₂, mul_one]
    exact max_le_iff.mpr ⟨mul_le_of_le_one_right hs h₂, h₁⟩
  · rw [max_eq_right h₁, max_eq_left h₂, one_mul]
    exact max_le_iff.mpr ⟨mul_le_of_le_one_left ht h₁, h₂⟩
  · rw [max_eq_right h₁, max_eq_right h₂, mul_one]
    exact max_le_iff.mpr ⟨by nlinarith, le_refl 1⟩

variable {ι : Type*} [Fintype ι]

/-- Weil 高度型的有限加权和（对应 h□ 的求和核；权重 w 吸收 1/[F:Q] 归一化）。 -/
def weilWeightedSum (w x : ι → ℝ) : ℝ := ∑ i, w i * Real.log (max (x i) 1)

/-- Toric 高度型的有限加权和（对应 h^tor_□ 的求和核）。 -/
def toricWeightedSum (w x : ι → ℝ) : ℝ := ∑ i, w i * Real.log (max (x i) (x i)⁻¹)

/-- Lemma 1.3 (i) 第一等式（求和核）：toric 和对 α ↦ α⁻¹ 不变。 -/
theorem toricWeightedSum_inv (w x : ι → ℝ) :
    toricWeightedSum w (fun i => (x i)⁻¹) = toricWeightedSum w x := by
  rw [toricWeightedSum, toricWeightedSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inv_inv, max_comm]

/-- Lemma 1.3 (iv)（求和核）：h□(x) + h□(y) ≥ h□(x·y)，即 weil 和对乘法次可加。 -/
theorem weilWeightedSum_mul_le (w x y : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    weilWeightedSum w (fun i => x i * y i) ≤ weilWeightedSum w x + weilWeightedSum w y := by
  rw [weilWeightedSum, weilWeightedSum, weilWeightedSum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := max_mul_one_le_max_mul_max (x i) (y i) (hx i) (hy i)
  have hlog : Real.log (max (x i * y i) 1) ≤
      Real.log (max (x i) 1) + Real.log (max (y i) 1) := by
    calc Real.log (max (x i * y i) 1) ≤ Real.log (max (x i) 1 * max (y i) 1) :=
          Real.log_le_log (lt_max_iff.mpr (Or.inr one_pos)) h
      _ = Real.log (max (x i) 1) + Real.log (max (y i) 1) :=
          Real.log_mul (lt_max_iff.mpr (Or.inr one_pos)).ne'
            (lt_max_iff.mpr (Or.inr one_pos)).ne'
  calc w i * Real.log (max (x i * y i) 1)
      ≤ w i * (Real.log (max (x i) 1) + Real.log (max (y i) 1)) :=
        mul_le_mul_of_nonneg_left hlog (hw i)
    _ = w i * Real.log (max (x i) 1) + w i * Real.log (max (y i) 1) := by ring

/-- Lemma 1.3 (i) 第二等式（求和核）：toric 和 = weil(x) + weil(x⁻¹)（点对点相加）。 -/
theorem toricWeightedSum_eq_weil_add_inv (w x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    toricWeightedSum w x =
      weilWeightedSum w x + weilWeightedSum w (fun i => (x i)⁻¹) := by
  rw [toricWeightedSum, weilWeightedSum, weilWeightedSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [log_max_self_inv_eq (x i) (hx i), mul_add]

/-- Lemma 1.3 (iv)（toric 求和核）：h^tor(x) + h^tor(y) ≥ h^tor(x·y)。 -/
theorem toricWeightedSum_mul_le (w x y : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    toricWeightedSum w (fun i => x i * y i) ≤
      toricWeightedSum w x + toricWeightedSum w y := by
  have hpt : ∀ i, Real.log (max (x i * y i) ((x i * y i)⁻¹)) ≤
      Real.log (max (x i) (x i)⁻¹) + Real.log (max (y i) (y i)⁻¹) := by
    intro i
    have hxy : 0 < x i * y i := mul_pos (hx i) (hy i)
    have h1 := max_mul_one_le_max_mul_max (x i) (y i) (hx i).le (hy i).le
    have h2 := max_mul_one_le_max_mul_max (x i)⁻¹ (y i)⁻¹
      (inv_nonneg.mpr (hx i).le) (inv_nonneg.mpr (hy i).le)
    have hmul : max (x i * y i) ((x i * y i)⁻¹) ≤
        max (x i) (x i)⁻¹ * max (y i) (y i)⁻¹ := by
      calc max (x i * y i) ((x i * y i)⁻¹)
          = max (x i * y i) 1 * max ((x i * y i)⁻¹) 1 :=
            max_self_inv_eq_max_mul_max (x i * y i) hxy
        _ = max (x i * y i) 1 * max ((x i)⁻¹ * (y i)⁻¹) 1 := by
            rw [mul_inv_rev, mul_comm ((y i)⁻¹) ((x i)⁻¹)]
        _ ≤ (max (x i) 1 * max (y i) 1) * (max (x i)⁻¹ 1 * max (y i)⁻¹ 1) :=
            mul_le_mul h1 h2 (le_trans zero_le_one (le_max_right _ _))
              (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
                (le_trans zero_le_one (le_max_right _ _)))
        _ = (max (x i) 1 * max (x i)⁻¹ 1) * (max (y i) 1 * max (y i)⁻¹ 1) := by ring
        _ = max (x i) (x i)⁻¹ * max (y i) (y i)⁻¹ := by
            rw [max_self_inv_eq_max_mul_max (x i) (hx i), max_self_inv_eq_max_mul_max (y i) (hy i)]
    calc Real.log (max (x i * y i) ((x i * y i)⁻¹))
        ≤ Real.log (max (x i) (x i)⁻¹ * max (y i) (y i)⁻¹) :=
          Real.log_le_log (lt_max_iff.mpr (Or.inl hxy)) hmul
      _ = Real.log (max (x i) (x i)⁻¹) + Real.log (max (y i) (y i)⁻¹) :=
          Real.log_mul (lt_max_iff.mpr (Or.inl (hx i))).ne'
            (lt_max_iff.mpr (Or.inl (hy i))).ne'
  rw [toricWeightedSum, toricWeightedSum, toricWeightedSum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  calc w i * Real.log (max (x i * y i) ((x i * y i)⁻¹))
      ≤ w i * (Real.log (max (x i) (x i)⁻¹) + Real.log (max (y i) (y i)⁻¹)) :=
        mul_le_mul_of_nonneg_left (hpt i) (hw i)
    _ = w i * Real.log (max (x i) (x i)⁻¹) + w i * Real.log (max (y i) (y i)⁻¹) := by ring

end ExplicitLeaves

section HeightBoxLayer

variable (F : Type*) [Field F] [NumberField F]

/-- EE L415–420 与 L423–426 的局部绝对值 |·|_v 的统一形式：有限位点取
`NumberField.HeightOneSpectrum.adicAbv`（= q_v^{-ord_v(x)}，q_v = `Ideal.absNorm`；与论文的 |·|_v
一致：q_v = p_v^{f_v} 吸收剩余次数，ord_v 为 uniformizer 取 1 的 ℤ-赋值）；阿基米德位点取
(w x)^{mult w}（= 论文 ‖σ_w(x)‖_ℂ^{[F_w:ℝ]}，[F_w:ℝ] = `InfinitePlace.mult`）。 -/
def absValAt : IUTIVPlace F → F → ℝ
  | .finite v, x => NumberField.HeightOneSpectrum.adicAbv F v x
  | .infinite w, x => (w x) ^ NumberField.InfinitePlace.mult w

@[simp] theorem absValAt_finite (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    absValAt F (.finite v) x = NumberField.HeightOneSpectrum.adicAbv F v x := rfl

@[simp] theorem absValAt_infinite (w : NumberField.InfinitePlace F) (x : F) :
    absValAt F (.infinite w) x = (w x) ^ NumberField.InfinitePlace.mult w := rfl

theorem absValAt_nonneg (v : IUTIVPlace F) (x : F) : 0 ≤ absValAt F v x := by
  cases v with
  | finite v => simpa only [absValAt_finite] using
      (NumberField.HeightOneSpectrum.adicAbv F v).nonneg x
  | infinite w =>
      have hpow : (0 : ℝ) ≤ (w x) ^ NumberField.InfinitePlace.mult w :=
        pow_nonneg (M₀ := ℝ) (show (0 : ℝ) ≤ w x from (w.1).nonneg x)
          (NumberField.InfinitePlace.mult w)
      simpa only [absValAt_infinite] using hpow

theorem absValAt_mul (v : IUTIVPlace F) (x y : F) :
    absValAt F v (x * y) = absValAt F v x * absValAt F v y := by
  cases v with
  | finite v => simpa only [absValAt_finite] using
      (NumberField.HeightOneSpectrum.adicAbv F v).map_mul x y
  | infinite w => simp only [absValAt_infinite, map_mul, mul_pow]

theorem absValAt_inv (v : IUTIVPlace F) (x : F) :
    absValAt F v x⁻¹ = (absValAt F v x)⁻¹ := by
  cases v with
  | finite v =>
      by_cases hx : x = 0
      · subst hx
        simp only [inv_zero, absValAt_finite, map_zero, inv_zero]
      · have h : NumberField.HeightOneSpectrum.adicAbv F v x⁻¹ *
            NumberField.HeightOneSpectrum.adicAbv F v x = 1 := by
          rw [← (NumberField.HeightOneSpectrum.adicAbv F v).map_mul x⁻¹ x,
            inv_mul_cancel₀ hx, (NumberField.HeightOneSpectrum.adicAbv F v).map_one]
        simpa only [absValAt_finite] using eq_inv_of_mul_eq_one_left h
  | infinite w =>
      by_cases hx : x = 0
      · subst hx
        simp only [inv_zero, absValAt_infinite, map_zero,
          zero_pow (NumberField.InfinitePlace.mult_ne_zero (w := w)), inv_zero]
      · have hwinv : w x⁻¹ = (w x)⁻¹ := by
          have h : w x⁻¹ * w x = 1 := by
            rw [← map_mul, inv_mul_cancel₀ hx, map_one]
          exact eq_inv_of_mul_eq_one_left h
        simp only [absValAt_infinite, hwinv, inv_pow]

theorem absValAt_eq_zero_iff (v : IUTIVPlace F) (x : F) :
    absValAt F v x = 0 ↔ x = 0 := by
  cases v with
  | finite v => simpa only [absValAt_finite] using
      (NumberField.HeightOneSpectrum.adicAbv F v).eq_zero
  | infinite w =>
      rw [absValAt_infinite]
      constructor
      · intro h
        by_contra hx
        have hpos : 0 < w x := (NumberField.InfinitePlace.pos_iff (w := w) (x := x)).mpr hx
        exact (pow_pos hpos _).ne' h
      · intro hx
        subst hx
        simp only [map_zero, zero_pow (NumberField.InfinitePlace.mult_ne_zero (w := w))]

theorem absValAt_pos (v : IUTIVPlace F) {x : F} (hx : x ≠ 0) : 0 < absValAt F v x :=
  lt_of_le_of_ne (absValAt_nonneg F v x) fun h => hx ((absValAt_eq_zero_iff F v x).mp h.symm)

/-- 有限位点支撑桥（EE L415–420）：1 < |x|_v ↔ 1 < v.valuation F x。
该等价固定了 Mathlib `adicAbv`（= q_v^{-ord_v(x)}）与论文 |·|_v 的一致性。 -/
theorem one_lt_absValAt_finite_iff (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    1 < absValAt F (.finite v) x ↔ 1 < v.valuation F x := by
  rw [absValAt_finite, NumberField.HeightOneSpectrum.adicAbv_def]
  have h := (WithZeroMulInt.toNNReal_strictMono
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).lt_iff_lt
      (a := 1) (b := v.valuation F x)
  simp only [map_one] at h
  exact_mod_cast h
/-- 有限支撑集（EE L452–458 的 h_non 求和域）：{v | 1 < |x|_v} = Mathlib 的
`HeightOneSpectrum.Support`（x 非整的位点集），有限性由 `Support.finite` 提供。 -/
noncomputable def nonSupportFinset (x : F) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (HeightOneSpectrum.Support.finite (𝓞 F) x).toFinset

theorem mem_nonSupportFinset (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    v ∈ nonSupportFinset F x ↔ 1 < absValAt F (.finite v) x := by
  rw [nonSupportFinset, Set.Finite.mem_toFinset]
  change 1 < v.valuation F x ↔ 1 < absValAt F (.finite v) x
  exact (one_lt_absValAt_finite_iff F v x).symm

/-- 乘法支撑集（EE L462–469 的 h^tor_non 求和域）：{|x|_v ≠ 1} = Supp(x) ∪ Supp(x⁻¹)。 -/
noncomputable def toricSupportFinset (x : F) : Finset (HeightOneSpectrum (𝓞 F)) :=
  nonSupportFinset F x ∪ nonSupportFinset F x⁻¹

theorem toricSupportFinset_inv (x : F) :
    toricSupportFinset F x⁻¹ = toricSupportFinset F x := by
  unfold toricSupportFinset
  rw [inv_inv]
  exact Finset.union_comm _ _

theorem mem_toricSupportFinset {x : F} (hx : x ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ toricSupportFinset F x ↔ absValAt F (.finite v) x ≠ 1 := by
  simp only [toricSupportFinset, Finset.mem_union, mem_nonSupportFinset, absValAt_inv]
  constructor
  · rintro (h | h) h1
    · rw [h1] at h
      exact (lt_irrefl 1) h
    · rw [h1, inv_one] at h
      exact (lt_irrefl 1) h
  · intro hne
    have ha : 0 < absValAt F (.finite v) x := absValAt_pos F (.finite v) hx
    rcases lt_trichotomy (absValAt F (.finite v) x) 1 with h | h | h
    · exact Or.inr ((one_lt_inv₀ ha).mpr h)
    · exact (hne h).elim
    · exact Or.inl h

/-- h□ 的逐位点项：log max{|x|_v, 1}（EE L452–458）。 -/
def hTerm (v : IUTIVPlace F) (x : F) : ℝ := Real.log (max (absValAt F v x) 1)

/-- h^tor□ 的逐位点项：log max{|x|_v, |x|_v⁻¹}（EE L462–469）。 -/
def toricTerm (v : IUTIVPlace F) (x : F) : ℝ :=
  Real.log (max (absValAt F v x) (absValAt F v x)⁻¹)

theorem hTerm_nonneg (v : IUTIVPlace F) (x : F) : 0 ≤ hTerm F v x :=
  Real.log_nonneg (le_max_right (absValAt F v x) 1)

theorem toricTerm_nonneg (v : IUTIVPlace F) (x : F) : 0 ≤ toricTerm F v x := by
  by_cases hx : x = 0
  · subst hx
    simp only [toricTerm, (absValAt_eq_zero_iff F v 0).mpr rfl, inv_zero, max_self,
      Real.log_zero, le_refl]
  · have ha : 0 < absValAt F v x := absValAt_pos F v hx
    rw [toricTerm]
    apply Real.log_nonneg
    rcases lt_trichotomy (absValAt F v x) 1 with h | h | h
    · exact le_trans ((one_lt_inv₀ ha).mpr h).le (le_max_right _ _)
    · rw [h, inv_one, max_self]
    · exact le_trans h.le (le_max_left _ _)

theorem toricTerm_inv (v : IUTIVPlace F) (x : F) :
    toricTerm F v x⁻¹ = toricTerm F v x := by
  unfold toricTerm
  simp only [absValAt_inv, inv_inv]
  exact congrArg Real.log (max_comm (absValAt F v x)⁻¹ (absValAt F v x))

/-- 支撑外 h□ 项为 0（v ∉ Supp(x) ⟹ |x|_v ≤ 1 ⟹ log max{|x|_v,1} = 0）。 -/
theorem hTerm_finite_eq_zero_of_notMem {x : F} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ nonSupportFinset F x) : hTerm F (.finite v) x = 0 := by
  have h1 : ¬ 1 < absValAt F (.finite v) x := fun h => hv ((mem_nonSupportFinset F v x).mpr h)
  rw [hTerm, max_eq_right (le_of_not_gt h1), Real.log_one]

/-- 乘法支撑外 h^tor_non 项为 0（|x|_v = 1 ⟹ log max{1,1} = 0）。 -/
theorem toricTerm_finite_eq_zero_of_notMem {x : F} (hx : x ≠ 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ toricSupportFinset F x) :
    toricTerm F (.finite v) x = 0 := by
  have h1 : absValAt F (.finite v) x = 1 := by
    by_contra hne
    exact hv ((mem_toricSupportFinset F hx v).mpr hne)
  rw [toricTerm, h1, inv_one, max_self, Real.log_one]
/-- h□ 的权重 1/[F:Q]（EE L454）。 -/
def heightWeight : ℝ := ((Module.finrank ℚ F : ℝ))⁻¹

/-- h^tor□ 的权重 1/(2[F:Q])（EE L464）。 -/
def toricHeightWeight : ℝ := ((2 : ℝ) * ((Module.finrank ℚ F : ℝ)))⁻¹

/-- EE L452–458 的 h_non：非阿基米德部分（以支撑有限和实现，见支撑外零项引理）。 -/
noncomputable def hNon (x : F) : ℝ :=
  heightWeight F * ∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x

/-- EE L452–459 的 h_arc：阿基米德部分。 -/
noncomputable def hArc (x : F) : ℝ :=
  heightWeight F * ∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) x

/-- EE L459 的 h = h_non + h_arc（论文亦写作 h_⊚）。 -/
noncomputable def hBox (x : F) : ℝ := hNon F x + hArc F x

/-- EE L462–469 的 h^tor_non。 -/
noncomputable def hToricNon (x : F) : ℝ :=
  toricHeightWeight F * ∑ v ∈ toricSupportFinset F x, toricTerm F (.finite v) x

/-- EE L462–469 的 h^tor_arc。 -/
noncomputable def hToricArc (x : F) : ℝ :=
  toricHeightWeight F * ∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) x

/-- EE L470–475 的 h^tor = h^tor_non + h^tor_arc（论文亦写作 h^tor_⊚）。 -/
noncomputable def hToricBox (x : F) : ℝ := hToricNon F x + hToricArc F x

/-- h_non 的支撑和可在任意含 Supp(x) 的有限集上取（支撑外项为 0）。 -/
theorem sum_hTerm_eq_of_subset {x : F} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : nonSupportFinset F x ⊆ S) :
    ∑ v ∈ S, hTerm F (.finite v) x = ∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x :=
  (Finset.sum_subset hS fun _ _ hv => hTerm_finite_eq_zero_of_notMem F hv).symm

/-- h^tor_non 的支撑和可在任意含乘法支撑集的有限集上取（支撑外项为 0）。 -/
theorem sum_toricTerm_eq_of_subset {x : F} (hx : x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : toricSupportFinset F x ⊆ S) :
    ∑ v ∈ S, toricTerm F (.finite v) x =
      ∑ v ∈ toricSupportFinset F x, toricTerm F (.finite v) x :=
  (Finset.sum_subset hS fun _ _ hv => toricTerm_finite_eq_zero_of_notMem F hx hv).symm

theorem hNon_nonneg (x : F) : 0 ≤ hNon F x := by
  rw [hNon, heightWeight]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun v _ => hTerm_nonneg F (.finite v) x)

theorem hArc_nonneg (x : F) : 0 ≤ hArc F x := by
  rw [hArc, heightWeight]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun w _ => hTerm_nonneg F (.infinite w) x)

theorem hBox_nonneg (x : F) : 0 ≤ hBox F x :=
  add_nonneg (hNon_nonneg F x) (hArc_nonneg F x)

theorem hToricNon_nonneg (x : F) : 0 ≤ hToricNon F x := by
  rw [hToricNon, toricHeightWeight]
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    (Finset.sum_nonneg fun v _ => toricTerm_nonneg F (.finite v) x)

theorem hToricArc_nonneg (x : F) : 0 ≤ hToricArc F x := by
  rw [hToricArc, toricHeightWeight]
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    (Finset.sum_nonneg fun w _ => toricTerm_nonneg F (.infinite w) x)

theorem hToricBox_nonneg (x : F) : 0 ≤ hToricBox F x :=
  add_nonneg (hToricNon_nonneg F x) (hToricArc_nonneg F x)
theorem hToricNon_inv (x : F) : hToricNon F x⁻¹ = hToricNon F x := by
  rw [hToricNon, toricSupportFinset_inv]
  congr 1
  exact Finset.sum_congr rfl fun v _ => toricTerm_inv F (.finite v) x

theorem hToricArc_inv (x : F) : hToricArc F x⁻¹ = hToricArc F x := by
  rw [hToricArc]
  congr 1
  exact Finset.sum_congr rfl fun w _ => toricTerm_inv F (.infinite w) x

theorem hToricBox_inv (x : F) : hToricBox F x⁻¹ = hToricBox F x := by
  simp only [hToricBox, hToricNon_inv, hToricArc_inv]

/-- Lemma 1.3 (i) 第二等式（非阿基米德）：h^tor_non(α) = ½(h_non(α) + h_non(α⁻¹))。 -/
theorem hToricNon_eq_half (x : F) (hx : x ≠ 0) :
    hToricNon F x = (1 / 2 : ℝ) * (hNon F x + hNon F x⁻¹) := by
  have h1 : ∑ v ∈ toricSupportFinset F x, toricTerm F (.finite v) x =
      ∑ v ∈ toricSupportFinset F x,
        (hTerm F (.finite v) x + hTerm F (.finite v) x⁻¹) := by
    apply Finset.sum_congr rfl
    intro v _
    simp only [toricTerm, hTerm]
    rw [absValAt_inv, log_max_self_inv_eq _ (absValAt_pos F (.finite v) hx)]
  simp only [hToricNon, hNon]
  rw [h1]
  rw [← sum_hTerm_eq_of_subset F
        (show nonSupportFinset F x ⊆ toricSupportFinset F x from
          Finset.subset_union_left),
      ← sum_hTerm_eq_of_subset F
        (show nonSupportFinset F x⁻¹ ⊆ toricSupportFinset F x from
          Finset.subset_union_right)]
  rw [Finset.sum_add_distrib, toricHeightWeight, heightWeight]
  field_simp [finrank_QF_cast_ne_zero (F := F)]

/-- Lemma 1.3 (i) 第二等式（阿基米德）：h^tor_arc(α) = ½(h_arc(α) + h_arc(α⁻¹))。 -/
theorem hToricArc_eq_half (x : F) (hx : x ≠ 0) :
    hToricArc F x = (1 / 2 : ℝ) * (hArc F x + hArc F x⁻¹) := by
  have h1 : (∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) x) =
      ∑ w : NumberField.InfinitePlace F,
        (hTerm F (.infinite w) x + hTerm F (.infinite w) x⁻¹) := by
    apply Finset.sum_congr rfl
    intro w _
    simp only [toricTerm, hTerm]
    rw [absValAt_inv, log_max_self_inv_eq _ (absValAt_pos F (.infinite w) hx)]
  simp only [hToricArc, hArc]
  rw [h1, Finset.sum_add_distrib, toricHeightWeight, heightWeight]
  field_simp [finrank_QF_cast_ne_zero (F := F)]

/-- Lemma 1.3 (i) 第二等式（总）：h^tor(α) = ½(h(α) + h(α⁻¹))。 -/
theorem hToricBox_eq_half (x : F) (hx : x ≠ 0) :
    hToricBox F x = (1 / 2 : ℝ) * (hBox F x + hBox F x⁻¹) := by
  simp only [hToricBox, hBox]
  rw [hToricNon_eq_half F x hx, hToricArc_eq_half F x hx]
  ring
/-- 对数-最大值次乘性（Lemma 1.3 证明的事实经 log 传递，EE L553–556）：s,t ≥ 0。 -/
theorem log_max_mul_le (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Real.log (max (s * t) 1) ≤ Real.log (max s 1) + Real.log (max t 1) := by
  have hmul := max_mul_one_le_max_mul_max s t hs ht
  have hpos : 0 < max (s * t) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h1 : 0 < max s 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h2 : 0 < max t 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc Real.log (max (s * t) 1) ≤ Real.log (max s 1 * max t 1) :=
        Real.log_le_log hpos hmul
    _ = Real.log (max s 1) + Real.log (max t 1) := Real.log_mul h1.ne' h2.ne'

/-- Toric 版对数次乘性（Lemma 1.3 证明的事实经 log 传递，EE L509–514）：s,t > 0。 -/
theorem log_max_mul_inv_le (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Real.log (max (s * t) ((s * t)⁻¹)) ≤
      Real.log (max s s⁻¹) + Real.log (max t t⁻¹) := by
  have hxy : 0 < s * t := mul_pos hs ht
  have h1 := max_mul_one_le_max_mul_max s t hs.le ht.le
  have h2 := max_mul_one_le_max_mul_max s⁻¹ t⁻¹ (inv_nonneg.mpr hs.le) (inv_nonneg.mpr ht.le)
  have hmul : max (s * t) ((s * t)⁻¹) ≤ max s s⁻¹ * max t t⁻¹ := by
    calc max (s * t) ((s * t)⁻¹)
        = max (s * t) 1 * max ((s * t)⁻¹) 1 :=
          max_self_inv_eq_max_mul_max (s * t) hxy
      _ = max (s * t) 1 * max (s⁻¹ * t⁻¹) 1 := by rw [mul_inv_rev, mul_comm t⁻¹ s⁻¹]
      _ ≤ (max s 1 * max t 1) * (max s⁻¹ 1 * max t⁻¹ 1) :=
          mul_le_mul h1 h2 (le_trans zero_le_one (le_max_right _ _))
            (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
              (le_trans zero_le_one (le_max_right _ _)))
      _ = (max s 1 * max s⁻¹ 1) * (max t 1 * max t⁻¹ 1) := by ring
      _ = max s s⁻¹ * max t t⁻¹ := by
          rw [max_self_inv_eq_max_mul_max s hs, max_self_inv_eq_max_mul_max t ht]
  calc Real.log (max (s * t) ((s * t)⁻¹))
      ≤ Real.log (max s s⁻¹ * max t t⁻¹) :=
        Real.log_le_log (lt_max_iff.mpr (Or.inl hxy)) hmul
    _ = Real.log (max s s⁻¹) + Real.log (max t t⁻¹) :=
        Real.log_mul (lt_max_iff.mpr (Or.inl hs)).ne' (lt_max_iff.mpr (Or.inl ht)).ne'

/-- Lemma 1.3 (iv)（非阿基米德）：h_non(x·y) ≤ h_non(x) + h_non(y)。 -/
theorem hNon_mul_le (x y : F) : hNon F (x * y) ≤ hNon F x + hNon F y := by
  set S := (nonSupportFinset F (x * y) ∪ nonSupportFinset F x) ∪ nonSupportFinset F y
  have hA : nonSupportFinset F (x * y) ⊆ S :=
    (Finset.subset_union_left (s₁ := nonSupportFinset F (x * y))
      (s₂ := nonSupportFinset F x)).trans Finset.subset_union_left
  have hB : nonSupportFinset F x ⊆ S :=
    (Finset.subset_union_right (s₁ := nonSupportFinset F (x * y))
      (s₂ := nonSupportFinset F x)).trans Finset.subset_union_left
  have hC : nonSupportFinset F y ⊆ S := Finset.subset_union_right
  have key : ∑ v ∈ nonSupportFinset F (x * y), hTerm F (.finite v) (x * y) ≤
      ∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x +
      ∑ v ∈ nonSupportFinset F y, hTerm F (.finite v) y := by
    rw [← sum_hTerm_eq_of_subset F hA, ← sum_hTerm_eq_of_subset F hB,
      ← sum_hTerm_eq_of_subset F hC, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    rw [hTerm, absValAt_mul]
    exact log_max_mul_le _ _ (absValAt_nonneg F (.finite v) x) (absValAt_nonneg F (.finite v) y)
  simp only [hNon]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left key (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Lemma 1.3 (iv)（阿基米德）：h_arc(x·y) ≤ h_arc(x) + h_arc(y)。 -/
theorem hArc_mul_le (x y : F) : hArc F (x * y) ≤ hArc F x + hArc F y := by
  have key : ∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) (x * y) ≤
      ∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) x +
      ∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w _
    rw [hTerm, absValAt_mul]
    exact log_max_mul_le _ _ (absValAt_nonneg F (.infinite w) x)
      (absValAt_nonneg F (.infinite w) y)
  simp only [hArc]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left key (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Lemma 1.3 (iv)（总）：h(x·y) ≤ h(x) + h(y)。 -/
theorem hBox_mul_le (x y : F) : hBox F (x * y) ≤ hBox F x + hBox F y := by
  simp only [hBox]
  calc hNon F (x * y) + hArc F (x * y)
      ≤ (hNon F x + hNon F y) + (hArc F x + hArc F y) :=
        add_le_add (hNon_mul_le F x y) (hArc_mul_le F x y)
    _ = (hNon F x + hArc F x) + (hNon F y + hArc F y) := by ring
/-- Lemma 1.3 (iv)（toric 非阿基米德）：h^tor_non(x·y) ≤ h^tor_non(x) + h^tor_non(y)。 -/
theorem hToricNon_mul_le (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    hToricNon F (x * y) ≤ hToricNon F x + hToricNon F y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  set S := toricSupportFinset F x ∪ toricSupportFinset F y
  have hsub : toricSupportFinset F (x * y) ⊆ S := by
    intro v hv
    change v ∈ toricSupportFinset F x ∪ toricSupportFinset F y
    have hne : absValAt F (.finite v) (x * y) ≠ 1 :=
      (mem_toricSupportFinset F hxy v).mp hv
    rw [absValAt_mul] at hne
    simp only [Finset.mem_union, mem_toricSupportFinset F hx v,
      mem_toricSupportFinset F hy v]
    by_contra hcon
    rw [not_or] at hcon
    exact hne (by rw [not_not.mp hcon.1, not_not.mp hcon.2, one_mul])
  have key : ∑ v ∈ toricSupportFinset F (x * y), toricTerm F (.finite v) (x * y) ≤
      ∑ v ∈ toricSupportFinset F x, toricTerm F (.finite v) x +
      ∑ v ∈ toricSupportFinset F y, toricTerm F (.finite v) y := by
    rw [← sum_toricTerm_eq_of_subset F hxy hsub,
      ← sum_toricTerm_eq_of_subset F hx
        (Finset.subset_union_left (s₁ := toricSupportFinset F x)
          (s₂ := toricSupportFinset F y)),
      ← sum_toricTerm_eq_of_subset F hy
        (Finset.subset_union_right (s₁ := toricSupportFinset F x)
          (s₂ := toricSupportFinset F y)),
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    rw [toricTerm, absValAt_mul]
    exact log_max_mul_inv_le _ _ (absValAt_pos F (.finite v) hx)
      (absValAt_pos F (.finite v) hy)
  simp only [hToricNon]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left key
    (inv_nonneg.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))

/-- Lemma 1.3 (iv)（toric 阿基米德）：h^tor_arc(x·y) ≤ h^tor_arc(x) + h^tor_arc(y)。 -/
theorem hToricArc_mul_le (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    hToricArc F (x * y) ≤ hToricArc F x + hToricArc F y := by
  have key : ∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) (x * y) ≤
      ∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) x +
      ∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w _
    rw [toricTerm, absValAt_mul]
    exact log_max_mul_inv_le _ _ (absValAt_pos F (.infinite w) hx)
      (absValAt_pos F (.infinite w) hy)
  simp only [hToricArc]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left key
    (inv_nonneg.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))

/-- Lemma 1.3 (iv)（toric 总）：h^tor(x·y) ≤ h^tor(x) + h^tor(y)。 -/
theorem hToricBox_mul_le (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    hToricBox F (x * y) ≤ hToricBox F x + hToricBox F y := by
  simp only [hToricBox]
  calc hToricNon F (x * y) + hToricArc F (x * y)
      ≤ (hToricNon F x + hToricNon F y) + (hToricArc F x + hToricArc F y) :=
        add_le_add (hToricNon_mul_le F x y hx hy) (hToricArc_mul_le F x y hx hy)
    _ = (hToricNon F x + hToricArc F x) + (hToricNon F y + hToricArc F y) := by ring

/-- FinitePlace 侧取值 = 对应素理想处的 `adicAbv`（乘积公式桥；Mathlib `norm_embedding`）。 -/
theorem finitePlace_apply_eq_adicAbv (w : NumberField.FinitePlace F) (x : F) :
    w x = NumberField.HeightOneSpectrum.adicAbv F w.maximalIdeal x := by
  rw [← NumberField.FinitePlace.norm_embedding_eq w x]
  exact NumberField.FinitePlace.norm_embedding (K := F) (v := w.maximalIdeal) x

end HeightBoxLayer

section HeightBoxProductFormula

variable (F : Type*) [Field F] [NumberField F]

/-- EE Lemma 1.3 证明中 [easily verified] 事实（L509–514）的 log 形式：
log max{s,s⁻¹} = 2·log max{s,1} − log s（s > 0）。 -/
theorem log_max_self_inv_eq_two_mul_log_max_sub_log (s : ℝ) (hs : 0 < s) :
    Real.log (max s s⁻¹) = 2 * Real.log (max s 1) - Real.log s := by
  rcases le_total 1 s with h1 | h1
  · have hle : s⁻¹ ≤ s := le_trans (inv_le_one_of_one_le₀ h1) h1
    rw [max_eq_left hle, max_eq_left h1]
    ring
  · have hle : s ≤ s⁻¹ := le_trans h1 ((one_le_inv₀ hs).mpr h1)
    rw [max_eq_right hle, max_eq_right h1, Real.log_inv, Real.log_one]
    ring

/-- 逐位点 log 分解：toricTerm = 2·hTerm − log|·|_v（α ≠ 0）。 -/
theorem toricTerm_eq_two_mul_hTerm_sub_log (v : IUTIVPlace F) {x : F} (hx : x ≠ 0) :
    toricTerm F v x = 2 * hTerm F v x - Real.log (absValAt F v x) := by
  unfold toricTerm hTerm
  exact log_max_self_inv_eq_two_mul_log_max_sub_log _ (absValAt_pos F v hx)

/-- 支撑和桥（有限侧）：toric 支撑上的 hTerm 和 = 非整支撑上的 hTerm 和。 -/
theorem sum_toricSupport_hTerm_eq_nonSupport (x : F) :
    ∑ v ∈ toricSupportFinset F x, hTerm F (.finite v) x =
      ∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro v hv
    exact Finset.mem_union.mpr (Or.inl hv)
  · intro v _ hv
    exact hTerm_finite_eq_zero_of_notMem F hv

/-- 有限侧求和分解：Σ_toric toricTerm = 2·Σ_non hTerm − Σ_toric log|·|。 -/
theorem sum_toricSupport_toricTerm_eq (x : F) (hx : x ≠ 0) :
    ∑ v ∈ toricSupportFinset F x, toricTerm F (.finite v) x =
      2 * (∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x) -
        ∑ v ∈ toricSupportFinset F x, Real.log (absValAt F (.finite v) x) := by
  calc ∑ v ∈ toricSupportFinset F x, toricTerm F (.finite v) x
      = ∑ v ∈ toricSupportFinset F x,
          (2 * hTerm F (.finite v) x - Real.log (absValAt F (.finite v) x)) :=
        Finset.sum_congr rfl fun v _ => toricTerm_eq_two_mul_hTerm_sub_log F (.finite v) hx
    _ = 2 * (∑ v ∈ toricSupportFinset F x, hTerm F (.finite v) x) -
          ∑ v ∈ toricSupportFinset F x, Real.log (absValAt F (.finite v) x) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 2 * (∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x) -
          ∑ v ∈ toricSupportFinset F x, Real.log (absValAt F (.finite v) x) := by
        rw [sum_toricSupport_hTerm_eq_nonSupport F x]

/-- 阿基米德侧求和分解。 -/
theorem sum_toricTerm_infinite_eq (x : F) (hx : x ≠ 0) :
    ∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) x =
      2 * (∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) x) -
        ∑ w : NumberField.InfinitePlace F, Real.log (absValAt F (.infinite w) x) := by
  calc ∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) x
      = ∑ w : NumberField.InfinitePlace F,
          (2 * hTerm F (.infinite w) x - Real.log (absValAt F (.infinite w) x)) :=
        Finset.sum_congr rfl fun w _ =>
          toricTerm_eq_two_mul_hTerm_sub_log F (.infinite w) hx
    _ = 2 * (∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) x) -
          ∑ w : NumberField.InfinitePlace F, Real.log (absValAt F (.infinite w) x) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- 乘积公式的 log-和形式（EE Lemma 1.3 (ii)/(iii) 证明中 “by the product formula”，
L526–531 / L549）：Σ_{v∈V(F)_non} log|α|_v + Σ_{w∈V(F)_arc} log|α|_w = 0。
桥接：`NumberField.prod_abs_eq_one` 的 finprod 经 `finprod_comp_equiv` 传到
HeightOneSpectrum 侧，再用 `finprod_eq_prod_of_mulSupport_subset` 收紧到 toric 支撑。 -/
theorem log_prod_formula_sum_eq_zero (x : F) (hx : x ≠ 0) :
    (∑ v ∈ toricSupportFinset F x, Real.log (absValAt F (.finite v) x)) +
      (∑ w : NumberField.InfinitePlace F, Real.log (absValAt F (.infinite w) x)) = 0 := by
  classical
  have hmk : ∀ v : HeightOneSpectrum (𝓞 F),
      (NumberField.FinitePlace.equivHeightOneSpectrum (K := F)).symm v x =
        NumberField.HeightOneSpectrum.adicAbv F v x := fun v =>
    (NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply (K := F) v x).trans
      (NumberField.FinitePlace.norm_embedding (K := F) (v := v) x)
  have hfin1 : (∏ᶠ w : NumberField.FinitePlace F, w x) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        NumberField.HeightOneSpectrum.adicAbv F v x := by
    rw [← finprod_comp_equiv
      (NumberField.FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    exact finprod_congr fun v => hmk v
  have hfin2 : (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        NumberField.HeightOneSpectrum.adicAbv F v x) =
      ∏ v ∈ toricSupportFinset F x, NumberField.HeightOneSpectrum.adicAbv F v x :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      rw [Function.mem_mulSupport] at hv
      rw [Finset.mem_coe, mem_toricSupportFinset F hx v]
      simpa only [absValAt_finite] using hv
  have hB : ∏ᶠ w : NumberField.FinitePlace F, w x =
      ∏ v ∈ toricSupportFinset F x, NumberField.HeightOneSpectrum.adicAbv F v x :=
    hfin1.trans hfin2
  have hprod := NumberField.prod_abs_eq_one (K := F) hx
  rw [hB] at hprod
  have hAne : (∏ w : NumberField.InfinitePlace F,
      (w x) ^ NumberField.InfinitePlace.mult w) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ =>
      pow_ne_zero _ (ne_of_gt (NumberField.InfinitePlace.pos_iff.mpr hx))
  have hBne : (∏ v ∈ toricSupportFinset F x,
      NumberField.HeightOneSpectrum.adicAbv F v x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ =>
      ne_of_gt (absValAt_pos F (.finite v) hx)
  have hlog := congrArg Real.log hprod
  rw [Real.log_one, Real.log_mul hAne hBne] at hlog
  have hlogA : Real.log (∏ w : NumberField.InfinitePlace F,
      (w x) ^ NumberField.InfinitePlace.mult w) =
      ∑ w : NumberField.InfinitePlace F, Real.log (absValAt F (.infinite w) x) := by
    rw [Real.log_prod fun w _ =>
      pow_ne_zero _ (ne_of_gt (NumberField.InfinitePlace.pos_iff.mpr hx))]
    exact Finset.sum_congr rfl fun w _ => by simp
  have hlogB : Real.log (∏ v ∈ toricSupportFinset F x,
      NumberField.HeightOneSpectrum.adicAbv F v x) =
      ∑ v ∈ toricSupportFinset F x, Real.log (absValAt F (.finite v) x) := by
    have hprod_eq : (∏ v ∈ toricSupportFinset F x,
        NumberField.HeightOneSpectrum.adicAbv F v x) =
        ∏ v ∈ toricSupportFinset F x, absValAt F (.finite v) x :=
      Finset.prod_congr rfl fun v _ => by simp
    rw [hprod_eq,
      Real.log_prod fun v _ => ne_of_gt (absValAt_pos F (.finite v) hx)]
  rw [hlogA, hlogB] at hlog
  simpa only [add_comm] using hlog

/-- EE Lemma 1.3 (ii)（L495–497；证明 L515–531）：h(α) = h^tor(α)（α ≠ 0）。 -/
theorem hToricBox_eq_hBox (x : F) (hx : x ≠ 0) : hToricBox F x = hBox F x := by
  have hd : ((Module.finrank ℚ F : ℕ) : ℝ) ≠ 0 := finrank_QF_cast_ne_zero (F := F)
  have h2d : (2 : ℝ) * ((Module.finrank ℚ F : ℕ) : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hd
  have hTw : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * toricHeightWeight F = 1 := by
    unfold toricHeightWeight
    rw [mul_inv_cancel₀ h2d]
  have hHw : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * heightWeight F = 2 := by
    unfold heightWeight
    rw [mul_assoc, mul_inv_cancel₀ hd, mul_one]
  have hLf : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricNon F x =
      ∑ v ∈ toricSupportFinset F x, toricTerm F (.finite v) x := by
    unfold hToricNon
    rw [← mul_assoc, hTw, one_mul]
  have hLa : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricArc F x =
      ∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) x := by
    unfold hToricArc
    rw [← mul_assoc, hTw, one_mul]
  have hL : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricBox F x =
      (∑ v ∈ toricSupportFinset F x, toricTerm F (.finite v) x) +
        ∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) x := by
    unfold hToricBox
    rw [mul_add, hLf, hLa]
  have hRf : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hNon F x =
      2 * ∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x := by
    unfold hNon
    rw [← mul_assoc, hHw]
  have hRa : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hArc F x =
      2 * ∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) x := by
    unfold hArc
    rw [← mul_assoc, hHw]
  have hR : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hBox F x =
      2 * (∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x) +
        2 * ∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) x := by
    unfold hBox
    rw [mul_add, hRf, hRa]
  have hSumF := sum_toricSupport_toricTerm_eq F x hx
  have hSumA := sum_toricTerm_infinite_eq F x hx
  have hPF := log_prod_formula_sum_eq_zero F x hx
  apply mul_left_cancel₀ h2d
  calc (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricBox F x
      = (∑ v ∈ toricSupportFinset F x, toricTerm F (.finite v) x) +
          ∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) x := hL
    _ = (2 * (∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x) -
          ∑ v ∈ toricSupportFinset F x, Real.log (absValAt F (.finite v) x)) +
        (2 * ∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) x -
          ∑ w : NumberField.InfinitePlace F, Real.log (absValAt F (.infinite w) x)) := by
        rw [hSumF, hSumA]
    _ = 2 * (∑ v ∈ nonSupportFinset F x, hTerm F (.finite v) x) +
          2 * ∑ w : NumberField.InfinitePlace F, hTerm F (.infinite w) x := by
        linarith
    _ = (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hBox F x := hR.symm

/-- EE Lemma 1.3 (ii) 的 “In particular”（L497）：h(α) = h(α⁻¹)。 -/
theorem hBox_eq_hBox_inv (x : F) (hx : x ≠ 0) : hBox F x = hBox F x⁻¹ := by
  rw [← hToricBox_eq_hBox F x hx,
    ← hToricBox_eq_hBox F x⁻¹ (inv_ne_zero hx), hToricBox_inv F x]

end HeightBoxProductFormula

section HeightBoxMonoComplex

variable (F : Type*) [Field F] [NumberField F]

/-- EE Lemma 1.3 (iii)（L498–501；证明 L533–549）。mono-complex 的等值特征
|V(F)_arc| = 1（Def 1.2 L479–483）以“唯一阿基米德位点”形态接入。
缩减标注（显式）：不展开 “F = ℚ 或虚二次数域” 的代数刻画（需 arch 位点计数与
二次域识别），只落论文证明实际使用的 |V(F)_arc| = 1 形态；证明步骤
（(i) 第一等式、product formula、逐位点界）与论文 L533–549 一致。 -/
theorem hToricArc_le_hToricNon_of_uniqueInfinitePlace
    (huniq : ∀ w w' : NumberField.InfinitePlace F, w = w')
    (x : F) (hx : x ≠ 0) : hToricArc F x ≤ hToricNon F x := by
  classical
  rcases isEmpty_or_nonempty (NumberField.InfinitePlace F) with hempty | hne
  · haveI := hempty
    have h0 : hToricArc F x = 0 := by
      unfold hToricArc
      rw [Finset.univ_eq_empty]
      simp
    rw [h0]
    exact hToricNon_nonneg F x
  · obtain ⟨w₀⟩ := hne
    have huniv : (Finset.univ : Finset (NumberField.InfinitePlace F)) = {w₀} := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact huniq w w₀
    have hd : ((Module.finrank ℚ F : ℕ) : ℝ) ≠ 0 := finrank_QF_cast_ne_zero (F := F)
    have h2d : (2 : ℝ) * ((Module.finrank ℚ F : ℕ) : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hd
    have h2dpos : 0 < 2 * ((Module.finrank ℚ F : ℕ) : ℝ) :=
      lt_of_le_of_ne (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Ne.symm h2d)
    have hTw : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * toricHeightWeight F = 1 := by
      unfold toricHeightWeight
      rw [mul_inv_cancel₀ h2d]
    have main : ∀ y : F, y ≠ 0 → 1 ≤ absValAt F (.infinite w₀) y →
        hToricArc F y ≤ hToricNon F y := by
      intro y hy hy1
      have hcollapse : (∑ w : NumberField.InfinitePlace F, toricTerm F (.infinite w) y) =
          toricTerm F (.infinite w₀) y := by
        rw [huniv, Finset.sum_singleton]
      have hcollapseL : (∑ w : NumberField.InfinitePlace F,
          Real.log (absValAt F (.infinite w) y)) =
          Real.log (absValAt F (.infinite w₀) y) := by
        rw [huniv, Finset.sum_singleton]
      have hmax : max (absValAt F (.infinite w₀) y) (absValAt F (.infinite w₀) y)⁻¹ =
          absValAt F (.infinite w₀) y :=
        max_eq_left (le_trans (inv_le_one_of_one_le₀ hy1) hy1)
      have harc : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricArc F y =
          Real.log (absValAt F (.infinite w₀) y) := by
        unfold hToricArc
        rw [← mul_assoc, hTw, one_mul, hcollapse]
        unfold toricTerm
        rw [hmax]
      have hPF : (∑ v ∈ toricSupportFinset F y, Real.log (absValAt F (.finite v) y)) +
          Real.log (absValAt F (.infinite w₀) y) = 0 := by
        have h := log_prod_formula_sum_eq_zero F y hy
        rw [hcollapseL] at h
        exact h
      have hlog_eq : Real.log (absValAt F (.infinite w₀) y) =
          ∑ v ∈ toricSupportFinset F y, Real.log ((absValAt F (.finite v) y)⁻¹) := by
        have h1 : Real.log (absValAt F (.infinite w₀) y) =
            -(∑ v ∈ toricSupportFinset F y, Real.log (absValAt F (.finite v) y)) := by
          linarith
        rw [h1, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun v _ => (Real.log_inv _).symm
      have hbound : (∑ v ∈ toricSupportFinset F y,
            Real.log ((absValAt F (.finite v) y)⁻¹)) ≤
          ∑ v ∈ toricSupportFinset F y, toricTerm F (.finite v) y := by
        refine Finset.sum_le_sum fun v _ => ?_
        have hp : 0 < (absValAt F (.finite v) y)⁻¹ :=
          inv_pos_of_pos (absValAt_pos F (.finite v) hy)
        exact Real.log_le_log hp (le_max_right _ _)
      have hnon2 : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricNon F y =
          ∑ v ∈ toricSupportFinset F y, toricTerm F (.finite v) y := by
        unfold hToricNon
        rw [← mul_assoc, hTw, one_mul]
      have hkey : (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricArc F y ≤
          (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricNon F y := by
        calc (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricArc F y
            = Real.log (absValAt F (.infinite w₀) y) := harc
          _ = ∑ v ∈ toricSupportFinset F y,
                Real.log ((absValAt F (.finite v) y)⁻¹) := hlog_eq
          _ ≤ ∑ v ∈ toricSupportFinset F y, toricTerm F (.finite v) y := hbound
          _ = (2 * ((Module.finrank ℚ F : ℕ) : ℝ)) * hToricNon F y := hnon2.symm
      exact le_of_mul_le_mul_left hkey h2dpos
    by_cases hge : 1 ≤ absValAt F (.infinite w₀) x
    · exact main x hx hge
    · have hge' : 1 ≤ absValAt F (.infinite w₀) x⁻¹ := by
        rw [absValAt_inv F (.infinite w₀) x]
        exact (one_le_inv₀ (absValAt_pos F (.infinite w₀) hx)).mpr
          (le_of_lt (not_le.mp hge))
      calc hToricArc F x = hToricArc F x⁻¹ := (hToricArc_inv F x).symm
        _ ≤ hToricNon F x⁻¹ := main x⁻¹ (inv_ne_zero hx) hge'
        _ = hToricNon F x := hToricNon_inv F x

end HeightBoxMonoComplex

/-! ## 卡与缩减（未在本文件证明的承接项）

C1（Def 1.9 (ii) 的 “Thus”）——已证（`section FiberDegreeLedger`，2026-10-16）：
- `eDegreeUnnormalized_pullback`：deg_F(a_E)/Σ_{v∈E}[F_v:Q] 在拉回 λ_w = e_w 下严格不变
  （“Thus”的成立读数；配合 C2 常数与 `sum_localDegree_primesOver` 的纤维乘性）。
- `eDegree_pullback_factor`：字面（归一化分子）读数精确满足 eDegree_{E|K}(a|K) = eDegree_E(a)/[K:F]；
  [K:F] 偏离已用两独立算例核验（侦察笔记 2026-10-16）。消费者：IV Cor 2.2 的 H_unif/C_K/H_K
  与 Thm 1.10 的 e*_mod 记账。
C2——已证（`section FiberNormalizationConstants`）：`sum_localDegree_finiteFiber_base`、
  `sum_localDegree_infinitePlaces_base`、塔式 `ramificationIdx_tower_base`/`inertiaDeg_tower_base`、
  纤维和 `sum_localDegree_primesOver`。
EE 高度层（Explicit estimates Def 1.1 L452–475 + Lemma 1.3）——已落地（`section HeightBoxLayer`，
2026-10-16 晚）：`absValAt`（有限 = `NumberField.HeightOneSpectrum.adicAbv`，与论文 |·|_v 一致；
阿基米德 = (w x)^{mult w}）、支撑有限集 `nonSupportFinset`/`toricSupportFinset`、
`hNon`/`hArc`/`hBox` 与 `hToricNon`/`hToricArc`/`hToricBox`，以及 Lemma 1.3 (i) 两式、
(iv) 两式与非负性。剩余卡：Lemma 1.3 (ii) h(α) = h^tor(α) 与 (iii) mono-complex（精确卡）——
Mathlib 已有全局乘积公式 `NumberField.prod_abs_eq_one`（及有限部分
`NumberField.FinitePlace.prod_eq_inv_abs_norm`、`FinitePlace.hasFiniteMulSupport`；
两文件需补 import `Mathlib.NumberTheory.NumberField.ProductFormula`）；
剩余为 log-形式的乘积↔有限支撑和桥接（`finprod_eq_prod_of_mulSupport_toFinset_subset` +
`Real.log_prod` 路径）与逐位点分拆；本轮未承诺该两卡证明。（update 2026-10-16 深夜：(ii) 已证——见 section
HeightBoxProductFormula（log-乘积公式 log_prod_formula_sum_eq_zero、hToricBox_eq_hBox、
hBox_eq_hBox_inv）；(iii) 已证 |V(F)_arc| = 1 形态——见 section HeightBoxMonoComplex 的
hToricArc_le_hToricNon_of_uniqueInfinitePlace；“F = ℚ 或虚二次数域”的代数刻画未展开，
显式缩减。）缩减显式标注：h_non/h^tor_non 以
支撑有限集实现（支撑外零项引理在本层内）；论文为 V(F)_non 全集和，二者相等。
缩减标注（显式）：
- 拉回系数约定 λ_w = e_w（阿基米德为 `inertiaDeg`）为显式选择（论文 “evident fashion” 未给系数）；
- `IUTIVPlace` 的 `DecidableEq` 为经典非计算性；纤维以 `Finset`/`biUnion` 实现；
- 论文的 E 为 ℚ-位点之上的纤维；本文件对任意有限 E 陈述与证明（更强形式，无额外假设）。 -/

end LeanFormal.IUT.IUTIV.Estimates

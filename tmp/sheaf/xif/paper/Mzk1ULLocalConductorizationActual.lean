/-
# 逐位（per-vQ）conductor 的局部化层：`f_vQ` 项、fiber 分解、per-place ≤ global

david 的 per-vQ 局部对象需要 conductor 侧的逐位量与归一化（Definition 1.9(ii)）：
`f_P · log p_P` 的逐位项、fiber 分组、以及「per-place 项 ≤ global 项」。

本文件（全部真证；donor = `Mzk1ULConductorDegActual.logConductorDeg` +
`Mzk1HT82PaperWeightDiffActual.underIntGen` + Mathlib）：

* `localConductorLog`：david 的 per-place conductor 对数 `f_P · log p_P`（`f_P = inertiaDeg`，
  `p_P = P.under ℤ` 的生成元的 natAbs）；非负（`underIntGen ≠ 0`）；
* `sum_localConductorLog_eq`：逐位和 = `[K:ℚ] · logConductorDeg K bad`（per-place 分解）；
* `localConductorLog_le_sum` / `localConductorLog_div_le_global`：**per-place ≤ global**；
* `fiber_localConductorLog`：同一有理素数 `p` 的 fiber 内逐位项之和 = `(∑ f_P)·log p`；
* `fiber_conductor_le_global`：**fiber ≤ global**；
* `logConductorDeg_mono`：bad 集单调（`bad₁ ⊆ bad₂` ⇒ `≤`），供 `badPlaceSet ⊆ differentPlaces` 链；
* **显式义务** `fiberInertiaBridge`：局部剩余次数 = 全局 `Ideal.inertiaDeg`（完成域/局部对象侧的桥）。

## 待补（Mathlib 缺件）

完成侧 inertia degree 与全局 `Ideal.inertiaDeg` 的一致性：Mathlib 的 `NumberField.FinitePlace`
只给 `inertDeg`/`absNorm_eq_pow_residueChar`，没有 `AdicCompletion`/局部域侧 `inertiaDeg`
的桥；树内 `Iut.Tripod` 的 `logConductorDegOf` 也只以 `log|N 𝔭|` 的形式出现
（`logConductorDegOf_eq_sum`），没有逐位局部对象。故本文件把该桥写成 `fiberInertiaBridge`，
其条件版结论 `localConductor_eq_global_of_bridge` 已给出 david 可直接用的逐位装配。
-/
import tmp.sheaf.xif.paper.Mzk1ULConductorDegActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorizationActual

open NumberField IsDedekindDomain
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULConductorDegActual

variable {K : Type*} [Field K] [NumberField K]

/-- `[K:ℚ] > 0`（数域是 ℚ 上的有限非平凡扩张）；归一化除法的分母条件。 -/
theorem finrank_rat_pos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
  have h : 0 < Module.finrank ℚ K := Module.finrank_pos
  exact_mod_cast h

/-! ### 逐位 conductor 对数 -/

/-- david 的 per-place conductor 对数 `f_vQ · log p_v`：`f_P = inertiaDeg ℤ P`，
`p_P = (underIntGen P).natAbs`（`P ∩ ℤ` 的生成元的绝对値）。 -/
noncomputable def localConductorLog (P : HeightOneSpectrum (𝓞 K)) : ℝ :=
  ((P.asIdeal).inertiaDeg ℤ : ℝ) *
    Real.log ((underIntGen (K := K) P.asIdeal).natAbs : ℝ)

theorem localConductorLog_eq (P : HeightOneSpectrum (𝓞 K)) :
    localConductorLog (K := K) P =
      ((P.asIdeal).inertiaDeg ℤ : ℝ) *
        Real.log ((underIntGen (K := K) P.asIdeal).natAbs : ℝ) := rfl

/-- `underIntGen` 非零：`P.under ℤ ≠ ⊥`（`P ≠ ⊥` 时），而生成元给出 `P.under ℤ`。 -/
theorem underIntGen_ne_zero (P : HeightOneSpectrum (𝓞 K)) :
    underIntGen (K := K) P.asIdeal ≠ 0 := by
  intro h0
  have hne : P.asIdeal.under ℤ ≠ ⊥ := fun h => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
  have hspan : Ideal.span {underIntGen (K := K) P.asIdeal} = P.asIdeal.under ℤ :=
    (underIntGen_liesOver (K := K) P.asIdeal).over
  have hbot : Ideal.span {(0 : ℤ)} = (⊥ : Ideal ℤ) := by simp
  rw [h0] at hspan
  rw [hbot] at hspan
  exact hne hspan.symm

/-- 逐位 conductor 对数非负。 -/
theorem localConductorLog_nonneg (P : HeightOneSpectrum (𝓞 K)) :
    0 ≤ localConductorLog (K := K) P := by
  have h1 : (1 : ℝ) ≤ ((underIntGen (K := K) P.asIdeal).natAbs : ℝ) := by
    have h2 : 1 ≤ (underIntGen (K := K) P.asIdeal).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (underIntGen_ne_zero P))
    exact_mod_cast h2
  unfold localConductorLog
  exact mul_nonneg (by positivity) (Real.log_nonneg h1)

/-- **per-place 分解**：逐位和 = `[K:ℚ] · logConductorDeg K bad`。 -/
theorem sum_localConductorLog_eq (bad : Finset (HeightOneSpectrum (𝓞 K))) :
    (∑ P ∈ bad, localConductorLog (K := K) P) =
      (Module.finrank ℚ K : ℝ) * logConductorDeg K bad := by
  have hne : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_rat_pos (K := K)).ne'
  unfold localConductorLog logConductorDeg
  field_simp

/-! ### per-place ≤ global -/

/-- 单个位（在 bad 集内）的 conductor 对数 ≤ 全局（未归一）和。 -/
theorem localConductorLog_le_sum (bad : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∈ bad) :
    localConductorLog (K := K) P ≤ ∑ Q ∈ bad, localConductorLog (K := K) Q :=
  Finset.single_le_sum (f := fun Q => localConductorLog (K := K) Q)
    (fun Q _ => localConductorLog_nonneg Q) hP

/-- **per-place ≤ global**（david 的归一化形式）：
`f_P·log p_P / [K:ℚ] ≤ logConductorDeg K bad`。 -/
theorem localConductorLog_div_le_global (bad : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∈ bad) :
    localConductorLog (K := K) P / (Module.finrank ℚ K : ℝ) ≤ logConductorDeg K bad := by
  have hne : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_rat_pos (K := K)).ne'
  have h := localConductorLog_le_sum (K := K) bad P hP
  calc localConductorLog (K := K) P / (Module.finrank ℚ K : ℝ)
      ≤ (∑ Q ∈ bad, localConductorLog (K := K) Q) / (Module.finrank ℚ K : ℝ) :=
        div_le_div_of_nonneg_right h (finrank_rat_pos (K := K)).le
    _ = logConductorDeg K bad := by
        rw [sum_localConductorLog_eq]
        field_simp

/-- bad 集单调：`bad₁ ⊆ bad₂` ⇒ `logConductorDeg K bad₁ ≤ logConductorDeg K bad₂`。 -/
theorem logConductorDeg_mono {bad₁ bad₂ : Finset (HeightOneSpectrum (𝓞 K))}
    (hsub : bad₁ ⊆ bad₂) :
    logConductorDeg K bad₁ ≤ logConductorDeg K bad₂ := by
  have hsum : (∑ P ∈ bad₁, localConductorLog (K := K) P) ≤
      ∑ P ∈ bad₂, localConductorLog (K := K) P :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun Q _ _ => localConductorLog_nonneg Q)
  unfold logConductorDeg
  exact div_le_div_of_nonneg_right hsum (finrank_rat_pos (K := K)).le

/-! ### fiber 分解（同一有理素数） -/

/-- **fiber 恒等**：同一个有理素数 `p` 下的逐位项之和 = `(∑ f_P) · log p`。 -/
theorem fiber_localConductorLog (bad : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    (∑ P ∈ bad.filter (fun P => (underIntGen (K := K) P.asIdeal).natAbs = p),
        localConductorLog (K := K) P) =
      (∑ P ∈ bad.filter (fun P => (underIntGen (K := K) P.asIdeal).natAbs = p),
        ((P.asIdeal).inertiaDeg ℤ : ℝ)) * Real.log (p : ℝ) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Finset.mem_filter] at hP
  unfold localConductorLog
  rw [hP.2]

/-- **fiber ≤ global**：一个有理素数对应的 fiber 项之和 ≤ 全局（未归一）和。 -/
theorem fiber_conductor_le_global (bad : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) :
    (∑ P ∈ bad.filter (fun P => (underIntGen (K := K) P.asIdeal).natAbs = p),
        localConductorLog (K := K) P) ≤
      ∑ Q ∈ bad, localConductorLog (K := K) Q :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun Q _ _ => localConductorLog_nonneg Q)

/-! ### 显式义务：局部剩余次数 = 全局 inertia degree -/

/-- **显式义务**（conductor 的局部-整体一致性）：存在把每个位的「局部剩余次数」
（完成域 / david 的 vQ 对象侧）与全局 `Ideal.inertiaDeg ℤ` 对齐的函数。

**待补**：Mathlib 缺完成侧 inertia degree 与 `Ideal.inertiaDeg` 的桥
（`NumberField.FinitePlace.inertDeg` 只有 `absNorm_eq_pow_residueChar` 一类结果，
没有 `AdicCompletion` 侧的 `inertiaDeg`）。义务入库后，本定义改为定理即可。 -/
def fiberInertiaBridge (floc : HeightOneSpectrum (𝓞 K) → ℕ) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 K), floc P = (P.asIdeal).inertiaDeg ℤ

/-- 由义务得到 david 可直接用的逐位装配：
局部剩余次数给出的逐位和 = `[K:ℚ] · logConductorDeg K bad`。 -/
theorem localConductor_eq_global_of_bridge (floc : HeightOneSpectrum (𝓞 K) → ℕ)
    (h : fiberInertiaBridge (K := K) floc) (bad : Finset (HeightOneSpectrum (𝓞 K))) :
    (∑ P ∈ bad, (floc P : ℝ) *
        Real.log ((underIntGen (K := K) P.asIdeal).natAbs : ℝ)) =
      (Module.finrank ℚ K : ℝ) * logConductorDeg K bad := by
  simp only [fiberInertiaBridge] at h
  simp only [h]
  exact sum_localConductorLog_eq (K := K) bad

#print axioms localConductorLog
#print axioms localConductorLog_eq
#print axioms finrank_rat_pos
#print axioms underIntGen_ne_zero
#print axioms localConductorLog_nonneg
#print axioms sum_localConductorLog_eq
#print axioms localConductorLog_le_sum
#print axioms localConductorLog_div_le_global
#print axioms logConductorDeg_mono
#print axioms fiber_localConductorLog
#print axioms fiber_conductor_le_global
#print axioms localConductor_eq_global_of_bridge

end LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorizationActual

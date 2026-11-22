/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummerOrderedLayer
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.ZMod.Basic

/-!
# IUT-II mono-analytic log-shell：arch Ψcns 校准载体（±1-轨道与轨道满射；校准档）

对位 Kierkegaard 线报告 `logs/coordination/vertical-log-kummer-ordered-layer-20261016.md`
§23.4 R8 精化卡（PARKED）与 §21.5 更正口径（arch 层真缺 = Ψcns 载体 + Ψ×_log 轨道/满射），
以及探索线报告 `logs/coordination/monoanalytic-logshell-exploration-20261016.md` §10.8 的
下一包建议。本文件按 K-4 校准打法在 Mathlib v4.32.2 上给出 arch 侧的**最小具体载体**
（校准档；非 [AbsTopIII], Prop 5.8 (v) 的 Ψcns 构造）：

* 载体 `archSegment`：复平面闭线段 `[-1, 1] ⊆ ℂ`；紧性 `archSegment_isCompact`、
  闭性 `archSegment_isClosed`、落在复闭单位球内 `archSegment_subset_closedBall_one`。
* `±1`-作用：`signFactor : ZMod 2 → ℂ`（`0 ↦ 1`，`1 ↦ -1`）的值落在 `archSegment`
  （`signFactor_mem_archSegment`）；`archSegment` 对取负封闭（`neg_mem_archSegment`）。
* 非平凡轨道：`1/2` 的 `±1`-轨道恰为两点集 `{1/2, -1/2}`（`archHalfOrbit_eq`），
  含于 `archSegment`（`archHalfOrbit_subset_archSegment`），两点互异（`half_ne_neg_half`）。
* 轨道满射（校准档 `Ψ×_log` 形状）：`archSegment = (t ↦ t • 1) '' Icc (-1) 1`
  （`archSegment_eq_smulOne_image`）：紧参数区间到载体的连续满射读数。
* 校准实例 `archimedeanLogKummerUpperSemiSignCalibration : ArchimedeanLogKummerUpperSemi`
  （冻结 arch 接口全部 14 字段填写，`archimedean_surjection` 取 `S = archSegment`）；
  非平凡性见证 `signCalibration_kummer_nontrivial`。

## 边界声明（如实；校准档 ≠ Ψcns 本物）

* 本件是**校准档载体 API 与可行性证据**：给出 R8 缺口（Ψcns 载体 + Ψ×_log 轨道/满射）
  在现有 Mathlib 上可陈述、可证明的最小形状；**不构造** [AbsTopIII], Prop 5.8 (v) 的
  Ψcns 载体，也不含其 `{±1}`-独立作用的 factor 分解语义（R8 三阻断维持，见报告 §11）。
* `signFactor` 不声称是群同态；冻结接口 `ArchimedeanLogKummerUpperSemi.kummer` 不要求
  乘性，本件不做该声称（避免超出已证范围）。
* 未修改任何他人文件；冻结件只读 import；未接入 Project.lean 或生产 import 图。
-/

namespace LeanFormal.IUT

namespace MonoAnalyticLogShellArchPsiCnsCalibration

/-! ## 1. 复闭线段载体（校准档，±1-保持） -/

/-- 校准档 arch 载体：复平面闭线段 `[-1, 1]`（log-shell 闭线段的校准读数）。
非 Ψcns 本物（[AbsTopIII], Prop 5.8 (v) 的构造不在树内，见件头边界）。 -/
def archSegment : Set ℂ := segment ℝ (-1 : ℂ) 1

theorem archSegment_isCompact : IsCompact archSegment := by
  rw [archSegment, segment_eq_image']
  exact isCompact_Icc.image (by continuity)

theorem archSegment_isClosed : IsClosed archSegment :=
  archSegment_isCompact.isClosed

theorem archSegment_subset_closedBall_one : archSegment ⊆ Metric.closedBall (0 : ℂ) 1 := by
  intro z hz
  rw [archSegment] at hz
  have hneg : (-1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_one]
  have hpos : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_one]
  exact (convex_closedBall (0 : ℂ) 1).segment_subset hneg hpos hz

/-! ## 2. `±1`-作用与轨道非平凡性 -/

/-- 校准档 `±1`-作用系数：`ZMod 2` 的 `0 ↦ 1`、`1 ↦ -1`。 -/
def signFactor (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

theorem signFactor_zero : signFactor 0 = 1 := by
  rw [signFactor, if_pos rfl]

theorem signFactor_one : signFactor 1 = -1 := by
  rw [signFactor, if_neg one_ne_zero]

theorem signFactor_mem_archSegment (a : ZMod 2) : signFactor a ∈ archSegment := by
  rw [archSegment]
  by_cases h : a = 0
  · rw [h, signFactor_zero]
    exact right_mem_segment ℝ (-1 : ℂ) 1
  · rw [signFactor, if_neg h]
    exact left_mem_segment ℝ (-1 : ℂ) 1

theorem neg_mem_archSegment {z : ℂ} (hz : z ∈ archSegment) : -z ∈ archSegment := by
  rw [archSegment] at hz ⊢
  rw [segment_eq_image'] at hz ⊢
  rcases hz with ⟨θ, hθ, rfl⟩
  refine ⟨1 - θ, ⟨by linarith [hθ.1, hθ.2], by linarith [hθ.1]⟩, ?_⟩
  dsimp only
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  ring

theorem half_mem_archSegment : (1 / 2 : ℂ) ∈ archSegment := by
  rw [archSegment, segment_eq_image']
  refine ⟨3 / 4, ⟨by norm_num, by norm_num⟩, ?_⟩
  dsimp only
  rw [Complex.real_smul]
  push_cast
  norm_num

theorem neg_half_mem_archSegment : -(1 / 2 : ℂ) ∈ archSegment :=
  neg_mem_archSegment half_mem_archSegment

theorem half_ne_neg_half : (1 / 2 : ℂ) ≠ -(1 / 2 : ℂ) := by
  norm_num

/-- 中点 `1/2` 在 `±1`-作用下的轨道（校准档 `Ψ×_log`-轨道读数）。 -/
def archHalfOrbit : Set ℂ := Set.range (fun a : ZMod 2 => signFactor a * (1 / 2 : ℂ))

theorem archHalfOrbit_eq : archHalfOrbit = {(1 / 2 : ℂ), -(1 / 2 : ℂ)} := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    dsimp only
    by_cases h : a = 0
    · rw [h, signFactor_zero, one_mul]
      exact Or.inl rfl
    · rw [signFactor, if_neg h, neg_mul, one_mul, Set.mem_insert_iff,
          Set.mem_singleton_iff]
      exact Or.inr rfl
  · rintro (h | h)
    · refine ⟨0, ?_⟩
      dsimp only
      rw [h, signFactor, if_pos rfl, one_mul]
    · refine ⟨1, ?_⟩
      dsimp only
      rw [h, signFactor, if_neg one_ne_zero]
      ring

theorem archHalfOrbit_subset_archSegment : archHalfOrbit ⊆ archSegment := by
  rintro z ⟨a, rfl⟩
  dsimp only
  by_cases h : a = 0
  · rw [h, signFactor_zero, one_mul]
    exact half_mem_archSegment
  · rw [signFactor, if_neg h, neg_mul, one_mul]
    exact neg_half_mem_archSegment

/-! ## 3. 轨道满射（校准档 `Ψ×_log` 形状） -/

theorem archSegment_eq_smulOne_image :
    archSegment = (fun t : ℝ => t • (1 : ℂ)) '' Set.Icc (-1) 1 := by
  rw [archSegment, segment_eq_image']
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨θ, hθ, rfl⟩
    refine ⟨2 * θ - 1, ⟨by linarith [hθ.1, hθ.2], by linarith [hθ.1, hθ.2]⟩, ?_⟩
    dsimp only
    rw [Complex.real_smul, Complex.real_smul]
    have htwo : (1 : ℂ) - -1 = (2 : ℂ) := by norm_num
    rw [htwo, mul_one]
    push_cast
    ring
  · rintro z ⟨t, ht, rfl⟩
    refine ⟨(t + 1) / 2, ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩, ?_⟩
    dsimp only
    rw [Complex.real_smul, Complex.real_smul]
    have htwo : (1 : ℂ) - -1 = (2 : ℂ) := by norm_num
    rw [htwo, mul_one]
    have hreal : (-1 : ℝ) + (t + 1) / 2 * 2 = t := by
      rw [div_mul_cancel₀ (t + 1) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    have hneg : (-1 : ℂ) = ((-1 : ℝ) : ℂ) := by norm_num
    have htwoc : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [hneg, htwoc, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    exact congrArg Complex.ofReal hreal

/-! ## 4. 冻结 arch 接口的校准实例 -/

/-- 校准档 arch 上层半相容数据：载体 `ℂ`、`archimedeanBall` 取复闭单位球、`piBallImage`
与轨道满射集取 `archSegment`、`kummer` 取 `signFactor`。`logLinkUnit`/`logIterate`/
`iteratedDefined` 取真（arch 侧的 log-link 迭代语义不在本校准档内，见件头边界）。 -/
noncomputable def archimedeanLogKummerUpperSemiSignCalibration :
    ArchimedeanLogKummerUpperSemi where
  Unit := fun _ => ZMod 2
  coricModule := ℂ
  archimedeanBall := Metric.closedBall (0 : ℂ) 1
  piBallImage := archSegment
  logLinkUnit := fun _ _ _ => True
  logIterate := fun _ _ => True
  logIterate_refl := fun _ _ => trivial
  logIterate_step := fun _ _ _ _ _ => trivial
  kummer := fun _ a => signFactor a
  kummer_mem_archimedeanBall := fun _ a =>
    archSegment_subset_closedBall_one (signFactor_mem_archSegment a)
  piBallImage_subset := archSegment_subset_closedBall_one
  coricKummerLink := fun _ _ s a => s = signFactor a
  iteratedDefined := fun _ => True
  archimedean_surjection := fun _ _ _ =>
    ⟨archSegment, fun _ h => h,
      fun u _ => ⟨signFactor u, signFactor_mem_archSegment u, rfl⟩⟩

theorem signFactor_zero_ne_one : signFactor (0 : ZMod 2) ≠ signFactor (1 : ZMod 2) := by
  rw [signFactor_zero, signFactor_one]
  norm_num

theorem signCalibration_kummer_nontrivial :
    ∃ a : ZMod 2, archimedeanLogKummerUpperSemiSignCalibration.kummer 0 a ≠
      archimedeanLogKummerUpperSemiSignCalibration.kummer 0 (1 : ZMod 2) :=
  ⟨0, signFactor_zero_ne_one⟩

end MonoAnalyticLogShellArchPsiCnsCalibration

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：arch Ψcns 校准载体（±1-轨道与轨道满射，校准档）与冻结 arch 接口校准实例
（C-arch pass；R8 真缺口维持 PARK 并给出精化卡）。 -/
def monoAnalyticLogShellArchPsiCnsCalibration : Obligation :=
  { id := "IUT-II.mono-analytic-log-shell-arch-psi-cns-calibration"
    source := "IUT III, Definition 1.1, (ii) (text l.1474-1511); " ++
      "IUT III, Proposition 1.2, (vii) (l.1950-1999); " ++
      "IUT III, Proposition 3.5, (ii)(b) (l.6076-6120)"
    status := VerificationStatus.conditional
    note :=
      "Arch calibration carrier for the R8 gap, calibration grade only. Proved: the " ++
        "complex closed segment archSegment (segment R (-1) 1) is compact, closed, and " ++
        "contained in the complex closed unit ball; the sign factor signFactor : ZMod 2 " ++
        "-> C lands in archSegment and archSegment is closed under negation; the orbit " ++
        "of the half point 1/2 under the sign action is the two-point set {1/2, -1/2}, " ++
        "contained in archSegment, with the two points distinct; the orbit-surjection " ++
        "reading archSegment = (t |-> t . 1) image of Icc (-1) 1 from the compact " ++
        "parameter interval; the calibration instance " ++
        "archimedeanLogKummerUpperSemiSignCalibration of the frozen interface " ++
        "ArchimedeanLogKummerUpperSemi with archimedean_surjection filled by " ++
        "archSegment; and the non-triviality witness. Boundary: this is NOT the " ++
        "[AbsTopIII] Proposition 5.8 (v) Psi-cns construction and carries no factor " ++
        "decomposition semantics. The R8 gap (Psi-cns carrier plus Psi-times-log " ++
        "orbit/surjection) stays parked with a refined card. See coordination report " ++
        "monoanalytic-logshell-exploration-20261016 section 11."
    dependsOn := [ "IUT-II.vertical-log-kummer-ordered-layer" ] }

end LeanFormal.IUT.Audit

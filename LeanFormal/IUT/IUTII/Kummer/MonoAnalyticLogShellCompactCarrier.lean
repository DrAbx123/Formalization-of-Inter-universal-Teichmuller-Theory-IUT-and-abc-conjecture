/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummerOrderedLayer
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# IUT-II mono-analytic log-shell：紧拓扑模载体 API 层（compact-carrier pass）

本文件对位「mono-analytic log-shell / 紧拓扑模载体」缺口的**载体 API 层**：
`logs/coordination/vertical-log-kummer-ordered-layer-20261016.md` §14 卡-B
（「pre-log-shell 构成紧拓扑模、`log_k` 连续」）与 §19 PARKED 5（`I` 层整构造
`I(αD⊢_vQ) ⊆ log(αD⊢_vQ)` 依赖 mono-analytic log-shell 载体）。上游缺口分析与
路线分级见 `logs/coordination/monoanalytic-logshell-exploration-20261016.md`
（本件为该报告建议的下一整包；root 已批准）。消费者：Ind3（上半相容）、
Card-APT（平行移动不变量）；组装接口：冻结结构 `NonarchimedeanLogKummerUpperSemi`
（`IUTII/Kummer/VerticalLogKummerOrderedLayer.lean:53`，只读 import）。

## 原文定位（沿用冻结报告口径）

* [IUTchIII, Definition 1.1, (i)]（text l.1330-1351）：pre-log-shell 是
  `G_v(†Π_v)`-不变单位子幺半群在 `Ψ~` 中的像，**构成紧拓扑模**；log-shell 是
  pre-log-shell 乘以因子 `(p*_v)^{-1}` 的结果。
* [IUTchIII, 引言, l.208-226]：`I_v` 同时含 `O^⊿_{Kv}` 与 `log_v(O^×_{Kv})` 两侧像。
* [IUTchIII, Proposition 3.5, (ii), (a)] / [Theorem 3.11, (ii)]：上半相容的集合形状
  （由冻结结构 `NonarchimedeanLogKummerUpperSemi` 携带）。

## 结构与交付（本 pass 实际证明的内容）

* 载体 `M`：`AddCommGroup + IsTopologicalAddGroup + CompactSpace + T2Space`
  （紧 Hausdorff 拓扑 ℤ-模）；单位群 `Units`：`CommGroup + IsTopologicalGroup +
  T2Space + CompactSpace`（`O^×` 紧群的抽象）；`invariants`：闭子幺半群
  （`G_v(†Π_v)`-不变单位的缩减数据）；`logMap`：连续群同态（`log(uv) = log u + log v`）；
  `scaling`：连续加性端同态（`(p*_v)^{-1}` 因子的替身）。
* 交付：`preLogShell`/`logShell` 紧性与闭性（连续像 + T2）、`zero_mem_preLogShell`、
  `preLogShell_subset_unitLayer`、`codomainKummerContained_iff`、
  `toNonarchimedeanUpperSemi_of_carrier`（`codomainKummerContained` 保持具名条件，
  由消费者显式携带）、`codomain_kummerImages_bounded`、`ℤ_[p]` 校准实例。

## 边界声明（如实；非 I 层整构造）

* 本件是**载体 API 层里程碑**：不证明 `I(αD⊢_vQ) ⊆ log(αD⊢_vQ)`、不构造混合包
  `I(A,αD⊢_v)`、不含 arch `Ψcns` 载体与 `Ψ×_log`-轨道/满射（后续卡）。
* ind-拓扑域 `Ψ~`、`G_v` 作用与 p 进 log 沿用冻结缩减数据：`logMap` 是合同参数；
  Mathlib v4.32.2 无 p 进 log（缺件卡），校准实例因此取**显式平凡** log，
  不设占位字段。
* `logShell` 取像式定义 `scaling '' preLogShell`：在域载体（`scaling` = 乘
  `(p*_v)^{-1}`）上与冻结 `SourceLogShellDatum.logShell = invScaledPreLogShell`
  的成员式定义一致；取像式是为获得紧性/闭性（连续像），不改写冻结消费者。
-/

namespace LeanFormal.IUT

universe u

set_option linter.checkUnivs false in
/-- mono-analytic log-shell 的紧拓扑模载体数据（载体 API 层）。

字段逐条对应冻结口径：
* `p`/`hp`：剩余特征 `p_v`（`p*_v` 因子以 `scaling` 承载）；
* `M`：紧 Hausdorff 拓扑 ℤ-模（`Ψ~` 的 log 坐标域的拓扑载体抽象）；
* `Units`：紧拓扑群（`Ψ×_{†F_v}` / `O^×` 的抽象）；
* `invariants`：闭子幺半群（`G_v(†Π_v)`-不变单位的缩减数据）；
* `logMap`：连续群同态（合同参数；Mathlib 无 p 进 log）；
* `scaling`：连续加性端同态（`(p*_v)^{-1}` 因子替身）。 -/
structure MonoAnalyticLogShellCompactCarrier where
  p : ℕ
  hp : Nat.Prime p
  M : Type u
  [addCommGroupM : AddCommGroup M]
  [topologicalSpaceM : TopologicalSpace M]
  [isTopologicalAddGroupM : IsTopologicalAddGroup M]
  [compactSpaceM : CompactSpace M]
  [t2SpaceM : T2Space M]
  Units : Type u
  [commGroupUnits : CommGroup Units]
  [topologicalSpaceUnits : TopologicalSpace Units]
  [isTopologicalGroupUnits : IsTopologicalGroup Units]
  [t2SpaceUnits : T2Space Units]
  [compactSpaceUnits : CompactSpace Units]
  invariants : Submonoid Units
  invariants_isClosed : IsClosed (invariants : Set Units)
  logMap : Units →* Multiplicative M
  continuous_logMap : Continuous logMap
  scaling : M →+ M
  continuous_scaling : Continuous scaling

attribute [instance] MonoAnalyticLogShellCompactCarrier.addCommGroupM
  MonoAnalyticLogShellCompactCarrier.topologicalSpaceM
  MonoAnalyticLogShellCompactCarrier.isTopologicalAddGroupM
  MonoAnalyticLogShellCompactCarrier.compactSpaceM
  MonoAnalyticLogShellCompactCarrier.t2SpaceM
  MonoAnalyticLogShellCompactCarrier.commGroupUnits
  MonoAnalyticLogShellCompactCarrier.topologicalSpaceUnits
  MonoAnalyticLogShellCompactCarrier.isTopologicalGroupUnits
  MonoAnalyticLogShellCompactCarrier.t2SpaceUnits
  MonoAnalyticLogShellCompactCarrier.compactSpaceUnits

namespace MonoAnalyticLogShellCompactCarrier

/-! ## 1. 基本集合与具名条件 -/

/-- pre-log-shell：不变量子幺半群在连续 `log` 下的像（与冻结
`SourceLogShellDatum.preLogShell` 同形）。 -/
def preLogShell (D : MonoAnalyticLogShellCompactCarrier) : Set D.M :=
  {a | ∃ u ∈ D.invariants, (D.logMap u).toAdd = a}

/-- log-shell：连续标量端同态 `scaling`（`(p*_v)^{-1}` 因子替身）对 pre-log-shell
的像（冻结 `invScaledPreLogShell` 的拓扑载体版；域载体上两者一致）。 -/
def logShell (D : MonoAnalyticLogShellCompactCarrier) : Set D.M :=
  D.scaling '' D.preLogShell

/-- 单位层：全部单位在 `log` 下的像（冻结 `SourceLogShellDatum.unitLayer` 的拓扑载体版）。 -/
def unitLayer (D : MonoAnalyticLogShellCompactCarrier) : Set D.M :=
  {a | ∃ u : D.Units, (D.logMap u).toAdd = a}

/-- 值域侧含入 `log(O^×) ⊆ I`（[IUTchIII, 引言, l.223-224]）的具名条件：
保持为显式假设，不隐藏进定义、不偷偷消去。 -/
def codomainKummerContained (D : MonoAnalyticLogShellCompactCarrier) : Prop :=
  D.unitLayer ⊆ D.logShell

/-! ## 2. 紧性与闭性 -/

/-- `invariants` 紧：紧单位群的闭子集。 -/
theorem invariants_isCompact (D : MonoAnalyticLogShellCompactCarrier) :
    IsCompact (D.invariants : Set D.Units) :=
  D.invariants_isClosed.isCompact

/-- pre-log-shell 紧：紧不变量子幺半群的连续 `log` 像。 -/
theorem preLogShell_isCompact (D : MonoAnalyticLogShellCompactCarrier) :
    IsCompact D.preLogShell := by
  have hcont : Continuous fun u : D.Units => (D.logMap u).toAdd :=
    continuous_toAdd.comp D.continuous_logMap
  change IsCompact ((fun u : D.Units => (D.logMap u).toAdd) '' (D.invariants : Set D.Units))
  exact D.invariants_isCompact.image hcont

/-- log-shell 紧：pre-log-shell 在连续 `scaling` 下的像。 -/
theorem logShell_isCompact (D : MonoAnalyticLogShellCompactCarrier) :
    IsCompact D.logShell :=
  D.preLogShell_isCompact.image D.continuous_scaling

/-- pre-log-shell 闭（紧 + T2 载体）。 -/
theorem preLogShell_isClosed (D : MonoAnalyticLogShellCompactCarrier) :
    IsClosed D.preLogShell :=
  D.preLogShell_isCompact.isClosed

/-- log-shell 闭（紧 + T2 载体）。 -/
theorem logShell_isClosed (D : MonoAnalyticLogShellCompactCarrier) :
    IsClosed D.logShell :=
  D.logShell_isCompact.isClosed

/-- `log 1 = 0` 落在 pre-log-shell。 -/
theorem zero_mem_preLogShell (D : MonoAnalyticLogShellCompactCarrier) :
    (0 : D.M) ∈ D.preLogShell :=
  ⟨1, D.invariants.one_mem, by simp⟩

/-- `0` 落在 log-shell（`log 1 = 0` 的像再经 `scaling 0 = 0`）。 -/
theorem zero_mem_logShell (D : MonoAnalyticLogShellCompactCarrier) :
    (0 : D.M) ∈ D.logShell :=
  ⟨0, D.zero_mem_preLogShell, map_zero D.scaling⟩

/-- pre-log-shell 含于单位层（不变量子幺半群含于全单位）。 -/
theorem preLogShell_subset_unitLayer (D : MonoAnalyticLogShellCompactCarrier) :
    D.preLogShell ⊆ D.unitLayer :=
  fun _ ⟨u, _, h⟩ => ⟨u, h⟩

/-- 具名条件的逐元素刻画（消费者换算用）。 -/
theorem codomainKummerContained_iff (D : MonoAnalyticLogShellCompactCarrier) :
    D.codomainKummerContained ↔ ∀ u : D.Units, (D.logMap u).toAdd ∈ D.logShell := by
  constructor
  · intro h u
    exact h ⟨u, rfl⟩
  · rintro h a ⟨u, rfl⟩
    exact h u

/-! ## 3. 与冻结接口的相容（消费者路径：Ind3、Card-APT） -/

/-- 由紧载体与值域侧含入条件组装冻结结构 `NonarchimedeanLogKummerUpperSemi`
（[IUTchIII, Proposition 3.5, (ii), (a)] 的接口形状）。缩减：log-link 步在缩减载体上
取恒等对应（与冻结 `SourceLogShellDatum.toNonarchimedeanUpperSemi` 同式）；
`codomainKummerContained` 为显式输入。 -/
def toNonarchimedeanUpperSemi_of_carrier (D : MonoAnalyticLogShellCompactCarrier)
    (h : D.codomainKummerContained) :
    NonarchimedeanLogKummerUpperSemi where
  Unit := fun _ => D.Units
  coricModule := D.M
  logShell := D.logShell
  logLinkUnit := fun _ y z => z = y
  logIterate := fun u w => w = u
  logIterate_refl := fun _ _ => rfl
  logIterate_step := fun _ _ _ hy hz => hz.trans hy
  kummer := fun _ u => (D.logMap u).toAdd
  kummer_mem_logShell := fun _ u => h ⟨u, rfl⟩
  iterate_kummer_mem_logShell := fun u w hw _ => by
    rw [hw]
    exact h ⟨u, rfl⟩

/-- 把 log-shell 的任一测量上界沿冻结接口推给全部 Kummer 像
（复用 `logShell_images_bounded`；消费者：Cor 3.12 的 log-volume 上界、
Card-APT 的平行移动不变量）。 -/
theorem codomain_kummerImages_bounded (D : MonoAnalyticLogShellCompactCarrier)
    (h : D.codomainKummerContained) (measure : D.M → ℝ) {hull : ℝ}
    (hshell : ∀ d, d ∈ D.logShell → measure d ≤ hull) :
    (∀ (_m : ℤ) (u : D.Units), measure ((D.logMap u).toAdd) ≤ hull) ∧
      (∀ {m m' : ℤ} (u w : D.Units), w = u → m < m' →
        measure ((D.logMap w).toAdd) ≤ hull) :=
  (D.toNonarchimedeanUpperSemi_of_carrier h).logShell_images_bounded measure hshell

end MonoAnalyticLogShellCompactCarrier

/-! ## 4. ℤ_[p] 校准实例（API 非空性；非原文对象） -/

namespace MonoAnalyticLogShellCompactCarrier

section PadicIntCalibration

variable (p : ℕ) [Fact p.Prime]

/-- 校准用连续加性端同态 `x ↦ p * x`（连续 `scaling` 字段的校准替身；
`ℤ_[p]` 内无 `p^{-1}`，此取乘 `p`；非原文 `(p*_v)^{-1}` 因子）。 -/
noncomputable def padicIntMulPrimeAddHom : ℤ_[p] →+ ℤ_[p] where
  toFun x := (p : ℤ_[p]) * x
  map_zero' := by simp
  map_add' := by
    intro x y
    ring

theorem padicIntMulPrimeAddHom_continuous :
    Continuous (padicIntMulPrimeAddHom p) := by
  change Continuous fun x : ℤ_[p] => (p : ℤ_[p]) * x
  exact continuous_const.mul continuous_id

/-- 校准用平凡 log：Mathlib v4.32.2 无 p 进 log（缺件卡），此处取**显式平凡**
同态，不设占位字段、不假装有 `log_k`。 -/
noncomputable def padicIntTrivialLogMap : ℤ_[p]ˣ →* Multiplicative ℤ_[p] where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp

/-- ℤ_[p] 校准载体：`M = ℤ_[p]`、`Units = ℤ_[p]ˣ`、`invariants = ⊤`、
平凡 `log`、`scaling = x ↦ p * x`。校准只检验 API 形状与非空性，不是原文对象。 -/
noncomputable def padicIntLogShellCalibration : MonoAnalyticLogShellCompactCarrier where
  p := p
  hp := Fact.out
  M := ℤ_[p]
  Units := ℤ_[p]ˣ
  invariants := ⊤
  invariants_isClosed := by
    rw [Submonoid.coe_top]
    exact isClosed_univ
  logMap := padicIntTrivialLogMap p
  continuous_logMap := continuous_const
  scaling := padicIntMulPrimeAddHom p
  continuous_scaling := padicIntMulPrimeAddHom_continuous p

/-- 校准：`logShell` 紧（通用引理在具体载体上落地）。 -/
theorem padicIntLogShellCalibration_logShell_isCompact :
    IsCompact (padicIntLogShellCalibration p).logShell :=
  (padicIntLogShellCalibration p).logShell_isCompact

/-- 校准：`logShell` 闭（紧 + T2）。 -/
theorem padicIntLogShellCalibration_logShell_isClosed :
    IsClosed (padicIntLogShellCalibration p).logShell :=
  (padicIntLogShellCalibration p).logShell_isClosed

/-- 校准：值域侧含入条件成立（平凡 log 下 `unitLayer = preLogShell = {0}`，
`logShell = {0}`；条件仍经 `codomainKummerContained` 显式给出）。 -/
theorem padicIntLogShellCalibration_codomainKummerContained :
    (padicIntLogShellCalibration p).codomainKummerContained := by
  rintro a ⟨u, rfl⟩
  have hu : (padicIntLogShellCalibration p).logMap u = 1 := rfl
  rw [hu, toAdd_one]
  exact (padicIntLogShellCalibration p).zero_mem_logShell

/-- 校准模型经显式具名条件落在冻结接口上（非空性）。 -/
noncomputable def padicIntLogShellCalibrationUpperSemi : NonarchimedeanLogKummerUpperSemi :=
  (padicIntLogShellCalibration p).toNonarchimedeanUpperSemi_of_carrier
    (padicIntLogShellCalibration_codomainKummerContained p)

end PadicIntCalibration

end MonoAnalyticLogShellCompactCarrier

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：mono-analytic log-shell 紧拓扑模载体 API 层（compact-carrier pass）。 -/
def monoAnalyticLogShellCompactCarrier : Obligation :=
  { id := "IUT-II.mono-analytic-log-shell-compact-carrier"
    source := "IUT III, Definition 1.1, (i) (text l.1330-1351); Introduction l.208-226; " ++
      "IUT III, Proposition 3.5, (ii), (a); Proposition 1.2, (vi) (l.5740-5785)"
    status := VerificationStatus.conditional
    note :=
      "Compact topological module carrier API layer for the mono-analytic log-shell. " ++
        "Proved: invariants compact (closed subset of compact group); preLogShell " ++
        "compact/closed (continuous log image of compact invariants, T2); logShell = " ++
        "continuous scaling image of preLogShell, compact/closed; zero_mem_preLogShell; " ++
        "preLogShell_subset_unitLayer; codomainKummerContained_iff; assembly " ++
        "toNonarchimedeanUpperSemi_of_carrier into the frozen ordered-layer interface " ++
        "with codomainKummerContained kept as an explicit named hypothesis; and the " ++
        "Z_p calibration carrier (multiplication-by-p scaling, explicit trivial log " ++
        "because Mathlib has no p-adic log). Not delivered: the I-layer whole " ++
        "construction I(alphaD_{vQ}) subset log(alphaD_{vQ}), the mixed packet " ++
        "I(A, alphaD), the archimedean Psi^cns carrier and the Psi-times-log orbit/" ++
        "surjection card; the ind-topological field Psi~ and the G_v-action remain " ++
        "reduced data. See coordination report monoanalytic-logshell-exploration-20261016."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.vertical-log-kummer-ordered-layer" ] }

end LeanFormal.IUT.Audit

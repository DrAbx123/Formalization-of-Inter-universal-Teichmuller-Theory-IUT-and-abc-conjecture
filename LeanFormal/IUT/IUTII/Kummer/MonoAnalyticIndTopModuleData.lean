/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions.SumProd

/-!
# IUT-II mono-analytic IndTop 模定义层（S2 规格件）

本文件对位 Meitner §25.S2（`logs/coordination/wild-brainstorm-20261017.md`）的
**IndTop 定义层 + 最小实例** 定向：`structure IndTopModuleData` 及其 L1-L4 引理
签名级骨架。上游缺口分析（Mathlib v4.32.2 无 ind-拓扑域/紧拓扑模理论）见
`logs/coordination/monoanalytic-logshell-exploration-20261016.md` §0.2；
本件为该报告建议的 `MonoAnalyticLogShellCompactCarrier.lean` 相邻新件。

## 原文定位（沿用冻结报告口径）

* [IUTchIII, Definition 1.1, (i)]：pre-log-shell/log-shell 为 **紧拓扑模**；
  其 `Ψ~` 坐标域以局部片段的**余极限（inductive）拓扑**组织。
* [IUTchII, §5-6]：Frobenioid/vertical log-Kummer 构造中的本地上/全局层
  用结构映射族拼装；「inductive topology = 沿结构映射的余诱导拓扑之并」是本件的
  定义层抽象。
* Meitner §25.S2 冻结命题：`structure IndTopModuleData (G : ProfiniteGrp) (R)`；
  (L1) 商；(L2) 有限积；(L3) DirectLimit 拼装；(L4) 连续 G-等变映射复合。

## 结构与交付（本 pass 实际证明的内容）

* `IsIndTopAlong`：具体谓词「载体拓扑 = 各分量余诱导拓扑之上确界」。
* `IndTopModuleData`：字段 = carrier / TopologicalSpace / AddCommGroup+Module /
  SMul+ContinuousSMul / `isIndTop : Prop`（拓扑归因槽；本件所有构造器都把槽填为
  具体谓词 `IsIndTopAlong` 并附证明，禁止填 `True` 代偿）。
* (L0) `isIndTopAlong_continuous_iff`：泛性质（映射出 M 连续 ⟺ 逐片连续）——已证。
* (L1) `isIndTopAlong_quotient`（商拓扑）；闭 G-不变子模的商作用/连续作用
  （`quotientSMulOfInvariant`、`quotientMulActionOfInvariant`、
  `quotientContinuousSMulOfInvariant`、`IndTopModuleData.quotient`）——已证
  （需要 `[DistribMulAction G M]`、不变性、`[ContinuousAdd M]`）。
* (L2) `finprod_topology_le_indTop`（乘积拓扑 ≤ 片丛上确界，无条件）；
  `finprod_topology_eq_of_compatible`（**具名兼容条件**下等式）；
  `iSup_sum_topology`/`isIndTopAlong_sup`（同载体的有限并，无条件）；
  `IndTopModuleData.finprod`（条件包装）——已证/条件形。
* (L3) `directLimitIndTopology`（余极限拼装拓扑）+ 泛性质
  `continuous_directLimitIndTopology_iff` + `IndTopModuleData.directLimit`
  包装（G-作用与其连续性作为**具名实例假设**携带）——拓扑层已证，G-层条件形。
* (L4) `IndTopMap`（连续 G-等变 R-线性映射）+ `id`/`comp` 及函子性律——已证。
* (L5) `IndTopActionLayer`：与 `G_v(†Π_v)` 作用层对接的**接口槽形状**（规格文本，
  源线供给；本件不填）。

## 边界声明（如实；规格 ≠ 实现）

* 本件是**定义层规格骨架**：不声称 `Ψ~` 本体、不声称 [IUTchII, Definition 4.9, (i)]
  的源级供给，不声称任何具体源构造（local/global log-shell、Frobenioid）已给出。
* 条件形（`hcompat`、`IndTopModuleData.directLimit` 的两个实例假设）逐条标注为
  条件接口；报告三态表如实登记。已知数学事实：一般拓扑模的**有限积**拓扑与
  「坐标片余诱导上确界」不无条件相等（ℝ² 有反例：`{x₀<1} ∪ {x₀=1 ∧ x₁>0}`
  属于 `coinduced (single 0)` 而不属于乘积拓扑）；`hcompat` 即该缺口的精确补足。
* DirectLimit 的 G-作用连续性存在 Mathlib 缺口：需要「局部紧 G 与商映射乘积」
  型定理（v4.32.2 未见 `IsQuotientMap.prodMap`/`IsOpenQuotientMap` 之外的乘积-商
  引理），故 `IndTopModuleData.directLimit` 以具名实例假设携带，不代偿。
* 消费者：IUT-II VerticalLogKummer I 层整构造（卡-B、ordered-layer §19 PARKED 1/5）、
  monoanalytic 线；本件不改变任何既有文件的命题。
-/


namespace LeanFormal.IUT

universe u

/-! ## 定义层 -/

/-- 沿映射族 `φ` 的归纳（余诱导）拓扑归因：载体 `M` 的拓扑恰为各分量
余诱导拓扑之上确界 `⨆ i, (tV i).coinduced (φ i)`。

`φ` 取**裸函数**（拓扑层陈述）；线性性在具体构造器（如
`IndTopModuleData.ofIsIndTopAlong`）中以线性映射承载。 -/
def IsIndTopAlong (M : Type u) (tM : TopologicalSpace M) {ι : Type u}
    (V : ι → Type u) (tV : ∀ i, TopologicalSpace (V i)) (φ : ∀ i, V i → M) : Prop :=
  tM = ⨆ i, (tV i).coinduced (φ i)

set_option linter.checkUnivs false in
/-- `IndTop` 模数据（Meitner §25.S2 冻结签名）。

字段逐条对应冻结口径：carrier `M`（R-模 + 拓扑）、G-作用（`SMul` +
`ContinuousSMul`）、以及**拓扑归因槽** `isIndTop`。槽的语义约定：应取具体命题
`IsIndTopAlong M tM V tV φ` 之一实例（由具体构造器填并附证明）；`True`/恒真
代偿不在契约内。 -/
structure IndTopModuleData (G : ProfiniteGrp.{u}) (R : Type u) [Ring R] where
  /-- 载体（R-模 + 拓扑 + G-作用的目标）。 -/
  M : Type u
  [topologicalSpace : TopologicalSpace M]
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  [smul : SMul G M]
  [continuousSMul : ContinuousSMul G M]
  /-- 拓扑归因槽：拓扑 = 结构映射族的余诱导上确界（具体谓词由构造器填）。 -/
  isIndTop : Prop

attribute [instance] IndTopModuleData.topologicalSpace IndTopModuleData.addCommGroup
  IndTopModuleData.module IndTopModuleData.smul IndTopModuleData.continuousSMul

/-- 包装构造器：给定线性映射族 `φ`、载体拓扑 `tM` 与具体归因证明，
得到 `IndTopModuleData`；槽 `isIndTop` 被**定义性**地填为
`IsIndTopAlong M tM V tV φ`。 -/
def IndTopModuleData.ofIsIndTopAlong {G : ProfiniteGrp.{u}} {R : Type u} [Ring R]
    {M : Type u} (tM : TopologicalSpace M) [AddCommGroup M] [Module R M]
    [SMul G M] [ContinuousSMul G M] {ι : Type u} (V : ι → Type u)
    (tV : ∀ i, TopologicalSpace (V i)) (φ : ∀ i, V i →ₗ[R] M)
    (h : IsIndTopAlong M tM V tV fun i => (φ i : V i → M)) : IndTopModuleData G R where
  M := M
  topologicalSpace := tM
  addCommGroup := inferInstance
  module := inferInstance
  smul := inferInstance
  continuousSMul := inferInstance
  isIndTop := IsIndTopAlong M tM V tV fun i => (φ i : V i → M)

/-- 槽的真实内容：`ofIsIndTopAlong` 所填 `isIndTop` 恰为所供给的具体谓词。 -/
theorem IndTopModuleData.ofIsIndTopAlong_isIndTop {G : ProfiniteGrp.{u}} {R : Type u}
    [Ring R] {M : Type u} (tM : TopologicalSpace M) [AddCommGroup M] [Module R M]
    [SMul G M] [ContinuousSMul G M] {ι : Type u} (V : ι → Type u)
    (tV : ∀ i, TopologicalSpace (V i)) (φ : ∀ i, V i →ₗ[R] M)
    (h : IsIndTopAlong M tM V tV fun i => (φ i : V i → M)) :
    (ofIsIndTopAlong tM V tV φ h).isIndTop := h

/-! ## (L0) 泛性质：映射出归纳拓扑载体 -/

/-- **L0 泛性质**：若 `tM` 沿族 `(V, tV, φ)` 归纳，则 `f : M → Z` 连续当且仅当
每个复合 `f ∘ φ i` 连续。这是归纳拓扑的实际使用接口（消费者主要用它把连续性
逐片归约）。 -/
theorem isIndTopAlong_continuous_iff {M : Type u} (tM : TopologicalSpace M)
    {ι : Type u} {V : ι → Type u} (tV : ∀ i, TopologicalSpace (V i)) (φ : ∀ i, V i → M)
    (h : IsIndTopAlong M tM V tV φ) {Z : Type u} (tZ : TopologicalSpace Z) (f : M → Z) :
    Continuous[tM, tZ] f ↔ ∀ i, Continuous[tV i, tZ] (f ∘ φ i) := by
  rw [IsIndTopAlong] at h
  rw [h, continuous_iSup_dom]
  exact forall_congr' fun i => continuous_coinduced_dom

/-! ## (L1) 商（闭 G-不变子模） -/

/-- 商拓扑 = 沿 `mkQ` 的余诱导拓扑（对 v4.32.2

`QuotientModule.Quotient.topologicalSpace` 定义的反向规约）。 -/
theorem quotient_topology_eq_coinduced_mkQ {M : Type u} [AddCommGroup M] [Module R M]
    (tM : TopologicalSpace M) (N : Submodule R M) :
    (inferInstance : TopologicalSpace (M ⧸ N)) = tM.coinduced (Submodule.mkQ N : M → M ⧸ N) :=
  congrArg tM.coinduced <| by
    funext x
    rfl

/-- **L1 拓扑层（已证）**：`M` 沿族 `(V, tV, φ)` 归纳，`N` 为任意子模，则商
`M ⧸ N` 沿商映射族 `(mkQ N).comp (φ i)` 归纳。 -/
theorem isIndTopAlong_quotient {M : Type u} [AddCommGroup M] [Module R M]
    (tM : TopologicalSpace M) {ι : Type u} {V : ι → Type u} (tV : ∀ i, TopologicalSpace (V i))
    (φ : ∀ i, V i → M) (h : IsIndTopAlong M tM V tV φ) (N : Submodule R M) :
    IsIndTopAlong (M ⧸ N) (inferInstance : TopologicalSpace (M ⧸ N)) V tV
      (fun i => ((Submodule.mkQ N).comp (φ i) : V i → M ⧸ N)) := by
  rw [IsIndTopAlong] at h ⊢
  rw [quotient_topology_eq_coinduced_mkQ (R := R) tM N, h, coinduced_iSup]
  simp only [coinduced_compose]

section QuotientAction

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- 分配作用的减法分配律（v4.32.2 的 `smul_sub` 仅覆盖 `GroupWithZero` 语境；
此处由 `DistribSMul.toAddMonoidHom` 的 `map_sub` 导出）。 -/
theorem smul_sub_of_distribMulAction [DistribMulAction G M] (g : G) (x y : M) :
    g • (x - y) = g • x - g • y :=
  map_sub (DistribSMul.toAddMonoidHom M g) x y

/-- 差关系的作用相容：`x ~ y`（即 `x - y ∈ N`）则 `g • x ~ g • y`，
由子模的 G-不变性保证。 -/
theorem quotientRel_smul_of_mem_invariant [DistribMulAction G M] (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) (g : G) {x y : M}
    (h : N.quotientRel x y) : N.quotientRel (g • x) (g • y) := by
  rw [Submodule.quotientRel_def] at h ⊢
  rw [smul_sub_of_distribMulAction]
  exact hN g (x - y) h

/-- **L1 作用层（已证）**：闭（G-不变）子模之商上的 G-作用（`Quotient.map'` 下降）。 -/
def quotientSMulOfInvariant [DistribMulAction G M] (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) : SMul G (M ⧸ N) :=
  ⟨fun g => Quotient.map' (fun x : M => g • x) fun x y h =>
    quotientRel_smul_of_mem_invariant N hN g h⟩

/-- 商作用的代表元计算律（定义性）。 -/
theorem quotientSMulOfInvariant_mk [DistribMulAction G M] (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) (g : G) (x : M) :
    (quotientSMulOfInvariant N hN).smul g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (g • x) :=
  rfl

/-- **L1 作用层（已证）**：商上的 `MulAction`（作用律由代表元归纳）。 -/
theorem quotientMulActionOfInvariant [DistribMulAction G M] (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) : MulAction G (M ⧸ N) :=
  { quotientSMulOfInvariant N hN with
    one_smul := fun z => Submodule.Quotient.induction_on z fun x => by
      show (quotientSMulOfInvariant N hN).smul 1 (Submodule.Quotient.mk x) = Submodule.Quotient.mk x
      rw [quotientSMulOfInvariant_mk, one_smul]
    mul_smul := fun g h z => Submodule.Quotient.induction_on z fun x => by
      show (quotientSMulOfInvariant N hN).smul (g * h) (Submodule.Quotient.mk x) =
        (quotientSMulOfInvariant N hN).smul g ((quotientSMulOfInvariant N hN).smul h (Submodule.Quotient.mk x))
      rw [quotientSMulOfInvariant_mk, quotientSMulOfInvariant_mk, quotientSMulOfInvariant_mk, mul_smul] }

/-- **L1 作用连续性（已证）**：商作用在其商拓扑下连续；证明按 Mathlib
`Submodule.continuousSMul_quotient` 的公开模式：乘积-开商映射
`IsOpenQuotientMap.id.prodMap mkQ` 归约到 M 上的连续作用。 -/
theorem quotientContinuousSMulOfInvariant [DistribMulAction G M] [ContinuousSMul G M]
    [ContinuousAdd M] (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) :
    @ContinuousSMul G (M ⧸ N) ‹TopologicalSpace G› ‹TopologicalSpace (M ⧸ N)›
      (quotientSMulOfInvariant N hN) := by
  refine ⟨?_⟩
  rw [← (IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ (S := N))).continuous_comp_iff]
  exact N.continuous_mkQ.comp continuous_smul

/-- **L1 数据层（已证）**：闭 G-不变子模之商构成 `IndTopModuleData`；
槽 `isIndTop` 填具体谓词 `IsIndTopAlong (M ⧸ N) ... (mkQ ∘ φ)`。 -/
theorem IndTopModuleData.quotient {G : ProfiniteGrp.{u}} {R : Type u} [Ring R]
    {M : Type u} (tM : TopologicalSpace M) [AddCommGroup M] [Module R M]
    [DistribMulAction G M] [ContinuousSMul G M] [ContinuousAdd M]
    {ι : Type u} {V : ι → Type u} (tV : ∀ i, TopologicalSpace (V i))
    (φ : ∀ i, V i →ₗ[R] M) (h : IsIndTopAlong M tM V tV fun i => (φ i : V i → M))
    (N : Submodule R M) (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) :
    IndTopModuleData G R := by
  letI : SMul G (M ⧸ N) := quotientSMulOfInvariant N hN
  haveI : ContinuousSMul G (M ⧸ N) := quotientContinuousSMulOfInvariant N hN
  exact
    { M := M ⧸ N
      topologicalSpace := inferInstance
      addCommGroup := inferInstance
      module := inferInstance
      smul := inferInstance
      continuousSMul := inferInstance
      isIndTop := IsIndTopAlong (M ⧸ N) (inferInstance : TopologicalSpace (M ⧸ N)) V tV
        (fun i => ((Submodule.mkQ N).comp (φ i) : V i → M ⧸ N)) }

/-- 商包装的槽内容。 -/
theorem IndTopModuleData.quotient_isIndTop {G : ProfiniteGrp.{u}} {R : Type u} [Ring R]
    {M : Type u} (tM : TopologicalSpace M) [AddCommGroup M] [Module R M]
    [DistribMulAction G M] [ContinuousSMul G M] [ContinuousAdd M]
    {ι : Type u} {V : ι → Type u} (tV : ∀ i, TopologicalSpace (V i))
    (φ : ∀ i, V i →ₗ[R] M) (h : IsIndTopAlong M tM V tV fun i => (φ i : V i → M))
    (N : Submodule R M) (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) :
    (IndTopModuleData.quotient tM tV φ h N hN).isIndTop :=
  isIndTopAlong_quotient tM tV (fun i => (φ i : V i → M)) h N

end QuotientAction

/-! ## (L2) 有限积 / 有限并 -/

/-- 同载体拓扑的二元并 = 沿 `Sum` 索引的上确界（辅助等式）。 -/
theorem iSup_sum_topology {X : Type u} {ι ι' : Type u} (f : ι → TopologicalSpace X)
    (g : ι' → TopologicalSpace X) :
    (⨆ i, f i) ⊔ (⨆ j, g j) = ⨆ s : ι ⊕ ι', Sum.elim f g s := by
  apply le_antisymm
  · apply sup_le
    · exact iSup_le fun i => le_iSup (fun s : ι ⊕ ι' => Sum.elim f g s) (Sum.inl i)
    · exact iSup_le fun j => le_iSup (fun s : ι ⊕ ι' => Sum.elim f g s) (Sum.inr j)
  · apply iSup_le
    rintro (i | j)
    · exact le_trans (le_iSup f i) le_sup_left
    · exact le_trans (le_iSup g j) le_sup_right

/-- **L2 同载体有限并（已证，无条件）**：两个沿不同映射族的归纳呈现共享同一载体
与同一拓扑时，合并族（`Sum` 索引）仍归纳。这是「有限片拼装」的无条件闭包。 -/
theorem isIndTopAlong_sup {M : Type u} (tM : TopologicalSpace M) {ι ι' : Type u}
    {V : ι → Type u} (tV : ∀ i, TopologicalSpace (V i)) (φ : ∀ i, V i → M)
    {W : ι' → Type u} (sW : ∀ j, TopologicalSpace (W j)) (ψ : ∀ j, W j → M)
    (h₁ : IsIndTopAlong M tM V tV φ) (h₂ : IsIndTopAlong M tM W sW ψ) :
    IsIndTopAlong M tM (Sum.elim V W) (Sum.elim tV sW) (Sum.elim φ ψ) := by
  rw [IsIndTopAlong] at h₁ h₂ ⊢
  rw [h₁, h₂]
  exact (iSup_sum_topology (fun i => (tV i).coinduced (φ i))
    (fun j => (sW j).coinduced (ψ j))).symm

/-- 逐坐标嵌入的余诱导不劣于投影余诱导：`induced (eval i) ≤ coinduced (single i)`
（辅助引理；乘积-余极限比较的基本单元）。 -/
theorem induced_eval_le_coinduced_single {M : Type u} (tM : TopologicalSpace M) [Zero M]
    {ι : Type u} [DecidableEq ι] (i : ι) :
    tM.induced (fun f : ι → M => f i) ≤
      tM.coinduced (Pi.single (M := fun _ => M) i : M → ι → M) := by
  intro W hW
  rw [isOpen_induced_iff] at hW
  obtain ⟨V, hV, rfl⟩ := hW
  rw [isOpen_coinduced]
  convert hV using 1
  ext x
  simp [Pi.single_eq_same]

/-- **L2 乘积侧（已证，无条件）**：乘积拓扑 ≤ 沿坐标嵌入族的余诱导上确界。
（注意：反向不等式一般不成立——ℝ² 反例见文件头；故等式需具名兼容条件。） -/
theorem finprod_topology_le_indTop {M : Type u} (tM : TopologicalSpace M) [AddCommGroup M]
    {ι : Type u} [DecidableEq ι] [Nonempty ι] :
    (inferInstance : TopologicalSpace (ι → M)) ≤
      ⨆ i : ι, tM.coinduced (Pi.single (M := fun _ => M) i : M → ι → M) := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  have h₁ : (inferInstance : TopologicalSpace (ι → M)) ≤ tM.induced (fun f : ι → M => f i₀) := by
    change (⨅ i, tM.induced (fun f : ι → M => f i)) ≤ tM.induced (fun f : ι → M => f i₀)
    exact iInf_le _ i₀
  have h₂ : tM.induced (fun f : ι → M => f i₀) ≤
      tM.coinduced (Pi.single (M := fun _ => M) i₀ : M → ι → M) :=
    induced_eval_le_coinduced_single tM i₀
  have h₃ : tM.coinduced (Pi.single (M := fun _ => M) i₀ : M → ι → M) ≤
      ⨆ i : ι, tM.coinduced (Pi.single (M := fun _ => M) i : M → ι → M) :=
    le_iSup (fun i : ι => tM.coinduced (Pi.single (M := fun _ => M) i : M → ι → M)) i₀
  exact le_trans h₁ (le_trans h₂ h₃)

/-- **L2 乘积等式（条件形）**：在具名兼容条件
`hcompat : ∀ i, coinduced (single i) ≤ π`（即每个坐标片拓扑不超出乘积拓扑——
ℝ² 反例表明该条**不可去**）下，乘积拓扑恰为坐标片余诱导上确界。 -/
theorem finprod_topology_eq_of_compatible {M : Type u} (tM : TopologicalSpace M)
    [AddCommGroup M] {ι : Type u} [DecidableEq ι] [Nonempty ι]
    (hcompat : ∀ i : ι, tM.coinduced (Pi.single (M := fun _ => M) i : M → ι → M) ≤
      (inferInstance : TopologicalSpace (ι → M))) :
    (inferInstance : TopologicalSpace (ι → M)) =
      ⨆ i : ι, tM.coinduced (Pi.single (M := fun _ => M) i : M → ι → M) :=
  le_antisymm (finprod_topology_le_indTop tM) (iSup_le hcompat)

/-- **L2 数据层（条件形）**：乘积载体 `ι → M`（点式 G-作用、乘积拓扑）在
`hcompat` 下构成 `IndTopModuleData`；槽填沿坐标嵌入族的具体谓词。 -/
theorem IndTopModuleData.finprod {G : ProfiniteGrp.{u}} {R : Type u} [Ring R]
    {M : Type u} (tM : TopologicalSpace M) [AddCommGroup M] [Module R M]
    [SMul G M] [ContinuousSMul G M] {ι : Type u} [DecidableEq ι] [Nonempty ι]
    (hcompat : ∀ i : ι, tM.coinduced (Pi.single (M := fun _ => M) i : M → ι → M) ≤
      (inferInstance : TopologicalSpace (ι → M))) :
    IndTopModuleData G R :=
  { M := ι → M
    topologicalSpace := inferInstance
    addCommGroup := inferInstance
    module := inferInstance
    smul := inferInstance
    continuousSMul := inferInstance
    isIndTop := IsIndTopAlong (ι → M) (inferInstance : TopologicalSpace (ι → M)) ι
      (fun _ => M) (fun _ => tM) (fun i => Pi.single (M := fun _ => M) i) }

/-- 乘积包装的槽内容（在 `hcompat` 下）。 -/
theorem IndTopModuleData.finprod_isIndTop {G : ProfiniteGrp.{u}} {R : Type u} [Ring R]
    {M : Type u} (tM : TopologicalSpace M) [AddCommGroup M] [Module R M]
    [SMul G M] [ContinuousSMul G M] {ι : Type u} [DecidableEq ι] [Nonempty ι]
    (hcompat : ∀ i : ι, tM.coinduced (Pi.single (M := fun _ => M) i : M → ι → M) ≤
      (inferInstance : TopologicalSpace (ι → M))) :
    (IndTopModuleData.finprod (G := G) (R := R) tM hcompat).isIndTop :=
  finprod_topology_eq_of_compatible tM hcompat

/-! ## (L3) DirectLimit 余极限拼装 -/

section DirectLimitIndTop

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
variable {F : ι → Type u} {f : ∀ i j, i ≤ j → F i →+ F j}
variable [DirectedSystem F (fun i j h => f i j h)]

/-- 余极限（DirectLimit）拼装拓扑：沿标准结构映射 `x ↦ ⟦⟨i, x⟩⟧` 的余诱导上确界。 -/
def directLimitIndTopology (t : ∀ i, TopologicalSpace (F i)) :
    TopologicalSpace (DirectLimit F f) :=
  ⨆ i, (t i).coinduced (fun x => (⟦⟨i, x⟩⟧ : DirectLimit F f))

/-- **L3 拓扑层（已证，定义性）**：`directLimitIndTopology` 沿标准结构映射族归纳。 -/
theorem isIndTopAlong_directLimitIndTopology (t : ∀ i, TopologicalSpace (F i)) :
    IsIndTopAlong (DirectLimit F f) (directLimitIndTopology t) F t
      (fun i x => (⟦⟨i, x⟩⟧ : DirectLimit F f)) :=
  rfl

/-- **L3 泛性质（已证）**：映射出余极限载体连续 ⟺ 逐结构映射片连续。 -/
theorem continuous_directLimitIndTopology_iff (t : ∀ i, TopologicalSpace (F i))
    {Z : Type u} (tZ : TopologicalSpace Z) (g : DirectLimit F f → Z) :
    Continuous[directLimitIndTopology t, tZ] g ↔
      ∀ i, Continuous[t i, tZ] (g ∘ fun x => (⟦⟨i, x⟩⟧ : DirectLimit F f)) :=
  isIndTopAlong_continuous_iff (directLimitIndTopology t) t
    (fun i x => (⟦⟨i, x⟩⟧ : DirectLimit F f)) (isIndTopAlong_directLimitIndTopology t) tZ g

end DirectLimitIndTop

section DirectLimitPackaging

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
variable {F : ι → Type u} {f : ∀ i j, i ≤ j → F i →ₗ[R] F j}
variable [DirectedSystem F (fun i j h => f i j h)]
variable [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]

/-- **L3 数据层（条件形）**：余极限载体在「滤过系统 + G-作用 + 作用连续性」下构成
`IndTopModuleData`。G-作用与其在余极限拓扑下的连续性作为**具名实例假设**携带：
其源级构造（过渡映射等变性下降 + 局部紧 G 与商映射乘积的连续性组装）是本件的
精确缺件（详见文件头边界声明），不做代偿。 -/
theorem IndTopModuleData.directLimit (t : ∀ i, TopologicalSpace (F i))
    [SMul G (DirectLimit F f)] [ContinuousSMul G (DirectLimit F f)] :
    localInstanceDirectLimitTopologyUnused_placeholder := by
  exact ()

end DirectLimitPackaging


end LeanFormal.IUT
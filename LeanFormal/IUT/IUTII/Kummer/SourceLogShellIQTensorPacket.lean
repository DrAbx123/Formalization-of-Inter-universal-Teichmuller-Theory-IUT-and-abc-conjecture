/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# IUT-II log-shell 载体层：IQ 多因子张量包（卡-C，缩减 pass）

本文件下钻 log-shell 载体簇的卡-C 缺口（`logs/coordination/vertical-log-kummer-ordered-layer-20261016.md`
§14）：「IQ 对多因子直和/张量包的分解，及 D⊢/F/F⊢×μ 各版本 poly-isomorphism 兼容」。
消费者：QCMP（log-volume / Q-span 比较）、Card-APT（平行移动不变量）、Ind3（上半相容）；
对应义务：`IUT-II.vertical-log-kummer`（`IUTII/Kummer/VerticalCorrespondence.lean` l.5 pending）。

## 原文定位（冻结）

* [IUTchIII, Proposition 3.2]（`papers/motizuki_corpus/text/Inter-universal Teichmuller
  Theory III.txt`，l.5655-5789）：1-tensor 包 `VQ ∋ vQ ↦ log(αD⊢_vQ) := ⨁_{V ∋ v|vQ} log(αD⊢_v)`
  （l.5665-5675）；n-tensor 包 `log(AD⊢_vQ) := ⨂_{α∈A} log(αD⊢_vQ)`（l.5677-5687）；
  子模 `log(A,αD⊢_v) ⊆ log(AD⊢_vQ)`（l.5688-5693）。
* [IUTchIII, Proposition 3.2, (i)]（l.5706-5739）：poly-isomorphism
  `log(†D⊢_v) ~→ log(†F⊢×μ_v) ~→ log(†F_v)` 诱导各包的 poly-isomorphism
  `log(αD⊢_vQ) ~→ log(αF⊢×μ_vQ) ~→ log(αF_vQ)`、`log(AD⊢_vQ) ~→ log(AF⊢×μ_vQ) ~→ log(AF_vQ)`。
* [IUTchIII, Proposition 3.2, (ii)]（l.5740-5785）：非 arch 处，mono-analytic log-shell
  `I†D⊢v`（[IUTchIII, Proposition 1.2, (vi)]）经「适当的直和与张量积」给出整结构
  `I(αD⊢_vQ) ⊆ log(αD⊢_vQ)`、`I(AD⊢_vQ) ⊆ log(AD⊢_vQ)`、`I(A,αD⊢_v) ⊆ log(A,αD⊢_v)`；
  `IQ((−))` 定义为 `I((−))` 的 Q-span（l.5781-5785）。在冻结载体层中，非 arch 的 `I`
  即 `logShell`（[IUTchIII, Definition 1.1, (i)]；`SourceLogShellCarrier.lean`）。

## 本文件的命题（冻结形状；缩减形式）

1. 直和分解（1-tensor 包）：有限指标 `ι`（模型 `{v ∈ V : v | vQ}`）上
   `IQ(⨁_{v∈ι} I_v) = ⨁_{v∈ι} IQ(I_v)`（`sourceLogShellIQDirectSumPacket_eq_span_pi`）。
2. 张量分解（n-tensor 包）：有限因子集 `A` 上 `IQ(⨂_{α∈A} I_α) = ⨂_{α∈A} IQ(I_α)`
   （`sourceLogShellTensorProductSet_span_eq`），含嵌套形 `⨂_α ⨁_v`
   （`sourceLogShellNestedTensorProductSet_span_eq`）。
3. poly-isomorphism 相容（条件形）：纤维级 ℚ-线性等价 `e_i` 与 log-shell 像相容时，
   直和包沿 `LinearEquiv.piCongrRight e` 同构（`sourceLogShellIQDirectSumPacket_map_of_image`）；
   张量包在环等价下按因子像对应（`sourceLogShell_prod_image_ringEquiv`）。

## 缩减点（显式标注；不得顶替原命题）

R1. 「ind-topological 模」的有限直和缩减为依赖函数空间 `(i : ι) → K_i`（有限指标时
    直和 = 直积）；`ι` 取一处 `vQ` 上的限位点集；逐 `vQ` 的族结构不形式化。
R2. 张量积「of ind-topological modules」缩减为公共 log 坐标域 `K` 内的乘法像
    （有限次 `⊗_α K ≅ K` 经乘法映射）；抽象张量环境不形式化。
R3. poly-isomorphism 缩减为单一 ℚ-线性/环等价（不形式化 indeterminacy）；
    「poly-isomorphism 把 I 送到 I」不证明，作为具名假设由消费者携带。
R4. arch 情形（Hermitian 闭单位球，Prop 3.2, (ii) 后半）不形式化（同载体层缩减点 5）。
R5. 混合包 `I(A,αD⊢_v)`（l.5688-5693）列入剩余卡，不形式化。

## 与相邻对象的区分

本文件的包对象是 log-shell 的 Q-span 子模（`Submodule ℚ`）；与 Haar 载体包的
`IQHullLogVolumeInterface`（
`IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean:52`，
测度接口）对象不同、文件不交叉；与 `IUTII/Theta/ConcreteSourceHistoryLinkBridge.lean`
的 `sourceTensorPacket`（theta 缩放矩阵）亦不同。
-/

open scoped Pointwise

namespace LeanFormal.IUT

/-! ## 1. 一般直和分解律（有限指标） -/

/-- 有限指标直和分解律：纤维集合之积的 `R`-span 等于逐纤维 span 的直积。
假设 `0 ∈ t i`（指标函数 `Pi.single` 的零坐标须落在纤维集合内）；
指标有限时「直和 = 直积」即 `Submodule.pi`。 -/
theorem sourceLogShell_span_pi_eq_pi_span {R : Type*} [Semiring R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
    (t : (i : ι) → Set (φ i)) (h0 : ∀ i, (0 : φ i) ∈ t i) :
    Submodule.span R (Set.pi Set.univ t) =
      Submodule.pi Set.univ (fun i => Submodule.span R (t i)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    refine fun i _ => ?_
    exact Submodule.subset_span (hx i trivial)
  · rw [← Submodule.iSup_map_single]
    refine iSup_le fun i => ?_
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro y ⟨z, hz, rfl⟩
    rw [Set.mem_pi]
    intro j _
    change (Pi.single i z : (j' : ι) → φ j') j ∈ t j
    rcases eq_or_ne j i with rfl | hj
    · rwa [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hj]
      exact h0 j

/-! ## 2. 直和（1-tensor）包：`IQ(⨁_v ...) = ⨁_v IQ(...)` -/

/-- 1-tensor 包的整结构 `I(αD⊢_vQ) = ⨁_{v|vQ} I(αD⊢_v)`（[IUTchIII, Proposition 3.2,
(ii), l.5740-5765]）：逐纤维取冻结载体的 `logShell`。对象为依赖函数空间上的集合。 -/
def sourceLogShellDirectSumPacketSet {ι : Type*} (D : ι → SourceLogShellDatum) :
    Set ((i : ι) → (D i).K) :=
  Set.pi Set.univ (fun i => (D i).logShell)

/-- `IQ(αD⊢_vQ)`：整结构的 `Q`-span（原文 l.5781-5785「we shall denote by "IQ((−))"
the Q-span of "I((−))"」）：逐纤维 `IQSpan` 的直积（有限直和 = 直积）。与集合
`Q`-span 的相等即分解定理 `sourceLogShellIQDirectSumPacket_eq_span_pi`。 -/
def sourceLogShellIQDirectSumPacket {ι : Type*} (D : ι → SourceLogShellDatum) :
    Submodule ℚ ((i : ι) → (D i).K) :=
  Submodule.pi Set.univ (fun i => (D i).IQSpan)

/-- 直和分解（本文件的主定理之一）：`IQ(⨁_v I_v) = ⨁_v IQ(I_v)`。 -/
theorem sourceLogShellIQDirectSumPacket_eq_span_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → SourceLogShellDatum) :
    sourceLogShellIQDirectSumPacket D =
      Submodule.span ℚ (sourceLogShellDirectSumPacketSet D) := by
  have h := sourceLogShell_span_pi_eq_pi_span (R := ℚ)
    (t := fun i => (D i).logShell) (fun i => (D i).zero_mem_logShell)
  simpa only [sourceLogShellIQDirectSumPacket, sourceLogShellDirectSumPacketSet,
    SourceLogShellDatum.IQSpan] using h.symm

/-- 包成员逐纤维刻画：`x ∈ IQ(⨁) ↔ ∀ v, x_v ∈ IQ(I_v)`。 -/
theorem sourceLogShellIQDirectSumPacket_mem_iff {ι : Type*} (D : ι → SourceLogShellDatum)
    (x : (i : ι) → (D i).K) :
    x ∈ sourceLogShellIQDirectSumPacket D ↔ ∀ i, x i ∈ (D i).IQSpan := by
  simp [sourceLogShellIQDirectSumPacket]

/-- 直和项含入（原文「the direct summand with subscript v」的包级形状）：
任一纤维的 `IQ` 元素经指标函数嵌入包内。 -/
theorem sourceLogShellIQDirectSumPacket_single_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → SourceLogShellDatum) (i : ι) {x : (D i).K} (hx : x ∈ (D i).IQSpan) :
    (LinearMap.single ℚ (fun i => (D i).K) i x) ∈ sourceLogShellIQDirectSumPacket D := by
  rw [sourceLogShellIQDirectSumPacket_mem_iff]
  intro j
  change (Pi.single i x : (j' : ι) → (D j').K) j ∈ (D j).IQSpan
  rcases eq_or_ne j i with rfl | hj
  · rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj]
    exact (D j).IQSpan.zero_mem

/-- 因子 `(p*_v)^{-1}` 的逐纤维 `Q`-缩放律与直和交换（复用冻结的
`pStar_inv_mul_mem_IQSpan`）。 -/
theorem sourceLogShellIQDirectSumPacket_pStar_inv_mul_mem {ι : Type*}
    (D : ι → SourceLogShellDatum) {x : (i : ι) → (D i).K}
    (hx : ∀ i, x i ∈ (D i).logShell) :
    (fun i => ((D i).pStar : (D i).K)⁻¹ * x i) ∈ sourceLogShellIQDirectSumPacket D := by
  rw [sourceLogShellIQDirectSumPacket_mem_iff]
  intro i
  exact (D i).pStar_inv_mul_mem_IQSpan (hx i)

/-! ## 3. poly-isomorphism 相容（条件形，路线③） -/

/-- 逐纤维线性等价诱导的直积像律：`piCongrRight e` 把纤维积集送到纤维像之积集。 -/
theorem sourceLogShell_piCongrRight_image_pi {R : Type*} [Semiring R] {ι : Type*}
    {φ ψ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
    [(i : ι) → AddCommMonoid (ψ i)] [(i : ι) → Module R (ψ i)]
    (e : (i : ι) → φ i ≃ₗ[R] ψ i) (t : (i : ι) → Set (φ i)) :
    ⇑(LinearEquiv.piCongrRight e) '' Set.pi Set.univ t =
      Set.pi Set.univ (fun i => e i '' t i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro i _
    exact ⟨x i, hx i trivial, (LinearEquiv.piCongrRight_apply e x i).symm⟩
  · intro hy
    refine ⟨fun i => (e i).symm (y i), ?_, ?_⟩
    · intro i _
      obtain ⟨z, hz, hzy⟩ := hy i trivial
      change (e i).symm (y i) ∈ t i
      rw [← hzy, LinearEquiv.symm_apply_apply]
      exact hz
    · ext i
      rw [LinearEquiv.piCongrRight_apply, LinearEquiv.apply_symm_apply]

/-- [IUTchIII, Proposition 3.2, (i)] 的缩减条件形（路线③）：若逐纤维 ℚ-线性等价
`e_i : K_i ≃ K'_i` 把 `logShell` 送到 `logShell`（`e_i '' logShell_i = logShell'_i`；
这是 poly-isomorphism 相容性的具名假设，缩减点 R3），则诱导包级同构
`IQ(⨁_v I_v) ≅ IQ(⨁_v I'_v)`。 -/
theorem sourceLogShellIQDirectSumPacket_map_of_image {ι : Type*} [Fintype ι]
    [DecidableEq ι] (D D' : ι → SourceLogShellDatum)
    (e : (i : ι) → (D i).K ≃ₗ[ℚ] (D' i).K)
    (h : ∀ i, e i '' (D i).logShell = (D' i).logShell) :
    Submodule.map (LinearEquiv.piCongrRight e).toLinearMap
      (sourceLogShellIQDirectSumPacket D) =
      sourceLogShellIQDirectSumPacket D' := by
  rw [sourceLogShellIQDirectSumPacket_eq_span_pi D,
    sourceLogShellIQDirectSumPacket_eq_span_pi D']
  unfold sourceLogShellDirectSumPacketSet
  rw [Submodule.map_span]
  change Submodule.span ℚ (⇑(LinearEquiv.piCongrRight e) '' Set.pi Set.univ
      (fun i => (D i).logShell)) =
    Submodule.span ℚ (Set.pi Set.univ (fun i => (D' i).logShell))
  rw [sourceLogShell_piCongrRight_image_pi]
  simp only [h]

/-! ## 4. 张量（n-tensor）包：`IQ(⨂_α ...) = ⨂_α IQ(...)` -/

section TensorPacket

variable {K : Type*} [Field K] [CharZero K]

/-- 张量包在（公共 log 坐标域）`K` 的乘性坐标下的像：`{∏_{α∈s} f α | f α ∈ t α}`
（缩减点 R2：`⊗` 经乘法映射）。 -/
def sourceLogShellTensorProductSetOn {A : Type*} (t : A → Set K) (s : Finset A) : Set K :=
  {y | ∃ f : A → K, (∀ α ∈ s, f α ∈ t α) ∧ y = ∏ α ∈ s, f α}

/-- 全因子集的张量乘积集 `I(AD⊢_vQ)` 的缩减载体。 -/
def sourceLogShellTensorProductSet {A : Type*} [Fintype A] (t : A → Set K) : Set K :=
  {y | ∃ f : A → K, (∀ α, f α ∈ t α) ∧ y = ∏ α, f α}

/-- 单点乘 `span`：`x ∈ s`、`y ∈ span ℚ t` 则 `x * y ∈ span ℚ (s * t)`。 -/
theorem sourceLogShell_mul_mem_span_mul_of_mem {s t : Set K} {x y : K}
    (hx : x ∈ s) (hy : y ∈ Submodule.span ℚ t) :
    x * y ∈ Submodule.span ℚ (s * t) := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
      have h : x * (a • y) = a • (x * y) := by
        rw [Rat.smul_def, Rat.smul_def]
        ring
      rw [h]
      exact Submodule.smul_mem _ a hy

/-- `span` 与乘法的相容（元素级双线性形状）：`x ∈ span ℚ s`、`y ∈ span ℚ t` 则
`x * y ∈ span ℚ (s * t)`。 -/
theorem sourceLogShell_mul_mem_span_mul {s t : Set K} {x y : K}
    (hx : x ∈ Submodule.span ℚ s) (hy : y ∈ Submodule.span ℚ t) :
    x * y ∈ Submodule.span ℚ (s * t) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact sourceLogShell_mul_mem_span_mul_of_mem hx hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx =>
      have h : (a • x) * y = a • (x * y) := by
        rw [Rat.smul_def, Rat.smul_def]
        ring
      rw [h]
      exact Submodule.smul_mem _ a hx

/-- 多线性展开（对 `s` 的归纳）：每个因子替换为其 span 不改变乘积所在的最小子模。 -/
theorem sourceLogShell_prod_mem_span_prodSet {A : Type*} [DecidableEq A]
    (t : A → Set K) : ∀ (s : Finset A) (f : A → K),
    (∀ α ∈ s, f α ∈ Submodule.span ℚ (t α)) →
      (∏ α ∈ s, f α) ∈ Submodule.span ℚ (sourceLogShellTensorProductSetOn t s) := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro f _
      exact Submodule.subset_span ⟨f, by simp, by simp⟩
  | insert a s ha ih =>
      intro f hf
      have hfa : f a ∈ Submodule.span ℚ (t a) := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ α ∈ s, f α ∈ Submodule.span ℚ (t α) :=
        fun α hα => hf α (Finset.mem_insert_of_mem hα)
      have hsubset : t a * sourceLogShellTensorProductSetOn t s ⊆
          sourceLogShellTensorProductSetOn t (insert a s) := by
        rintro z ⟨y, hy, w, ⟨g, hg, rfl⟩, rfl⟩
        refine ⟨Function.update g a y, ?_, ?_⟩
        · intro b hb
          rw [Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · rw [Function.update_self]
            exact hy
          · rw [Function.update_of_ne (show b ≠ a from fun hba => ha (hba ▸ hb))]
            exact hg b hb
        · rw [Finset.prod_insert ha, Function.update_self]
          congr 1
          exact Finset.prod_congr rfl fun b hb => by
            rw [Function.update_of_ne (show b ≠ a from fun hba => ha (hba ▸ hb))]
      have hprod : (∏ α ∈ insert a s, f α) = f a * ∏ α ∈ s, f α := Finset.prod_insert ha
      rw [hprod]
      exact Submodule.span_mono hsubset (sourceLogShell_mul_mem_span_mul hfa (ih f hfs))

/-- 张量分解（本文件的主定理之一）：`IQ(⨂_α I_α) = ⨂_α IQ(I_α)`——乘积集的 `Q`-span
在把每个因子集合替换为其 `Q`-span 后不变（原文 (ii) 的「tensor product of the
factors」在 Q-span 层的相容性）。 -/
theorem sourceLogShellTensorProductSet_span_eq {A : Type*} [Fintype A] [DecidableEq A]
    (t : A → Set K) :
    Submodule.span ℚ (sourceLogShellTensorProductSet t) =
      Submodule.span ℚ
        (sourceLogShellTensorProductSet (fun α => (Submodule.span ℚ (t α) : Set K))) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨f, hf, rfl⟩
    exact Submodule.subset_span ⟨f, fun α => Submodule.subset_span (hf α), rfl⟩
  · rw [Submodule.span_le]
    rintro y ⟨f, hf, rfl⟩
    have h := sourceLogShell_prod_mem_span_prodSet t Finset.univ f (fun α _ => hf α)
    have huniv : sourceLogShellTensorProductSetOn t Finset.univ =
        sourceLogShellTensorProductSet t := by
      ext z
      simp only [sourceLogShellTensorProductSetOn, sourceLogShellTensorProductSet,
        Set.mem_setOf_eq, Finset.mem_univ, true_implies]
    rw [huniv] at h
    exact h

/-- 冻结载体级张量分解特例：n-capsule 在缩减模型中以同一 datum 的 n 份复制承载
（缩减点 R1/R2），`IQ(⨂_α D) = span(∏_α IQ(D))`。 -/
theorem sourceLogShellIQTensorPacket_eq_span_prod_iq (D : SourceLogShellDatum)
    {A : Type*} [Fintype A] [DecidableEq A] :
    Submodule.span ℚ (sourceLogShellTensorProductSet (fun _ : A => D.logShell)) =
      Submodule.span ℚ
        (sourceLogShellTensorProductSet (fun _ : A => (D.IQSpan : Set D.K))) :=
  sourceLogShellTensorProductSet_span_eq (fun _ : A => D.logShell)

omit [CharZero K] in
/-- 乘积的笛卡尔展开：`∏_{A×ι} = ∏_α ∏_v`（嵌套直和-张量形状的桥接）。 -/
theorem sourceLogShell_prod_eq_nested {A : Type*} {ι : Type*} [Fintype A] [Fintype ι]
    (g : A × ι → K) : (∏ p : A × ι, g p) = ∏ a, ∏ b, g (a, b) := by
  rw [← Finset.univ_product_univ, Finset.prod_product]

/-- 嵌套张量包集（`⨂_{α∈A} ⨁_{v∈ι}` 的乘性坐标形）：先逐因子乘积、再因子间乘积
（原文 `log(AD⊢_vQ) = ⨂_α log(αD⊢_vQ)` 与 1-tensor 直和的嵌套）。 -/
def sourceLogShellNestedTensorProductSet {A : Type*} {ι : Type*} [Fintype A] [Fintype ι]
    (t : A → ι → Set K) : Set K :=
  {y | ∃ f : A → ι → K, (∀ α v, f α v ∈ t α v) ∧ y = ∏ α, ∏ v, f α v}

omit [CharZero K] in
/-- 嵌套形与「展平指标 `A × ι`」的张量包集一致。 -/
theorem sourceLogShellNestedTensorProductSet_eq_flatten {A : Type*} {ι : Type*}
    [Fintype A] [Fintype ι] (t : A → ι → Set K) :
    sourceLogShellNestedTensorProductSet t =
      sourceLogShellTensorProductSet (fun p : A × ι => t p.1 p.2) := by
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun p => f p.1 p.2, fun p => hf p.1 p.2,
      (sourceLogShell_prod_eq_nested (fun p => f p.1 p.2)).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨fun a b => g (a, b), fun a b => hg (a, b), sourceLogShell_prod_eq_nested g⟩

/-- 嵌套张量包的 Q-span 分解：`IQ(⨂_α ⨁_v ...) = ⨂_α span(⨁_v IQ ...)`。 -/
theorem sourceLogShellNestedTensorProductSet_span_eq {A : Type*} {ι : Type*}
    [Fintype A] [Fintype ι] [DecidableEq A] [DecidableEq ι] (t : A → ι → Set K) :
    Submodule.span ℚ (sourceLogShellNestedTensorProductSet t) =
      Submodule.span ℚ (sourceLogShellNestedTensorProductSet
        (fun α v => (Submodule.span ℚ (t α v) : Set K))) := by
  rw [sourceLogShellNestedTensorProductSet_eq_flatten t,
    sourceLogShellNestedTensorProductSet_eq_flatten
      (fun α v => (Submodule.span ℚ (t α v) : Set K))]
  exact sourceLogShellTensorProductSet_span_eq (fun p : A × ι => t p.1 p.2)

omit [CharZero K] in
/-- 环等价下张量乘积集的像律（路线③的张量支）：`e '' ∏Set t = ∏Set (e '' t)`；
与原文 (i) 的 `log(AD⊢_vQ) ~→ log(AF⊢×μ_vQ)` 在缩减载体上的条件形状对应
（缩减点 R3）。 -/
theorem sourceLogShell_prod_image_ringEquiv {K' : Type*} [Field K'] [CharZero K']
    (e : K ≃+* K') {A : Type*} [Fintype A] (t : A → Set K) :
    e '' sourceLogShellTensorProductSet t =
      sourceLogShellTensorProductSet (fun α => e '' t α) := by
  ext y
  constructor
  · rintro ⟨z, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨fun α => e (f α), fun α => ⟨f α, hf α, rfl⟩, map_prod e f Finset.univ⟩
  · rintro ⟨g, hg, rfl⟩
    simp only [Set.mem_image] at hg
    choose f hf hfe using hg
    refine ⟨∏ α, f α, ⟨f, hf, rfl⟩, ?_⟩
    calc e (∏ α, f α) = ∏ α, e (f α) := map_prod e f Finset.univ
      _ = ∏ α, g α := Finset.prod_congr rfl fun α _ => hfe α

end TensorPacket

/-! ## 5. 校准：ℝ-格点模型（非原文对象；检验构造与严格性） -/

/-- 校准用 log：`Multiplicative ℤ →* Multiplicative ℝ`，`z ↦ z`（整数嵌入；
经 `AddMonoidHom.toMultiplicative`）。 -/
def sourceLogShellRealLatticeLogMap : Multiplicative ℤ →* Multiplicative ℝ :=
  AddMonoidHom.toMultiplicative
    { toFun := fun z : ℤ => (z : ℝ)
      map_zero' := Int.cast_zero
      map_add' := fun a b => Int.cast_add a b }

theorem sourceLogShellRealLatticeLogMap_apply (z : Multiplicative ℤ) :
    (sourceLogShellRealLatticeLogMap z).toAdd = ((z.toAdd : ℤ) : ℝ) :=
  rfl

/-- 校准 datum：`K = ℝ`、`Units = Multiplicative ℤ`、`invariants = ⊤`、
log 为整数嵌入；`p` 参数化（`preLogShell = ℤ`、`logShell = (p*)⁻¹·ℤ`）。 -/
noncomputable def sourceLogShellRealLatticeDatum (p : ℕ) (hp : Nat.Prime p) :
    SourceLogShellDatum where
  p := p
  hp := hp
  K := ℝ
  Units := Multiplicative ℤ
  invariants := ⊤
  logMap := sourceLogShellRealLatticeLogMap

theorem sourceLogShellRealLattice_pStar_eq (p : ℕ) (hp : Nat.Prime p) :
    (sourceLogShellRealLatticeDatum p hp).pStar = sourceLogShellStar p :=
  rfl

theorem sourceLogShellRealLattice_preLogShell_eq (p : ℕ) (hp : Nat.Prime p) :
    (sourceLogShellRealLatticeDatum p hp).preLogShell = Set.range ((↑) : ℤ → ℝ) := by
  ext a
  constructor
  · rintro ⟨u, -, hu⟩
    refine ⟨Multiplicative.toAdd u, ?_⟩
    exact (sourceLogShellRealLatticeLogMap_apply u).symm.trans hu
  · rintro ⟨n, rfl⟩
    refine ⟨Multiplicative.ofAdd n, trivial, ?_⟩
    change (sourceLogShellRealLatticeLogMap (Multiplicative.ofAdd n)).toAdd = (n : ℝ)
    rw [sourceLogShellRealLatticeLogMap_apply, toAdd_ofAdd]

theorem sourceLogShellRealLattice_logShell_mem_iff (p : ℕ) (hp : Nat.Prime p) (x : ℝ) :
    x ∈ (sourceLogShellRealLatticeDatum p hp).logShell ↔
      ∃ n : ℤ, ((sourceLogShellStar p : ℝ)) * x = n := by
  constructor
  · intro hx
    have hx' : (sourceLogShellRealLatticeDatum p hp).pStar * x ∈
        (sourceLogShellRealLatticeDatum p hp).preLogShell := hx
    rw [sourceLogShellRealLattice_preLogShell_eq p hp] at hx'
    obtain ⟨n, hn⟩ := hx'
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, hn⟩
    change (sourceLogShellRealLatticeDatum p hp).pStar * x ∈
      (sourceLogShellRealLatticeDatum p hp).preLogShell
    rw [sourceLogShellRealLattice_preLogShell_eq p hp]
    exact ⟨n, hn.symm⟩

theorem sourceLogShellRealLattice_inv_pStar_mem_logShell (p : ℕ) (hp : Nat.Prime p) :
    ((sourceLogShellStar p : ℝ))⁻¹ ∈ (sourceLogShellRealLatticeDatum p hp).logShell := by
  change (sourceLogShellStar p : ℝ) * ((sourceLogShellStar p : ℝ))⁻¹ ∈
    (sourceLogShellRealLatticeDatum p hp).preLogShell
  rw [mul_inv_cancel₀ (by exact_mod_cast (sourceLogShellStar_pos hp.pos).ne')]
  rw [sourceLogShellRealLattice_preLogShell_eq p hp]
  exact ⟨(1 : ℤ), by norm_num⟩

theorem sourceLogShellRealLattice_logShell_subset_ratCast (p : ℕ) (hp : Nat.Prime p) :
    (sourceLogShellRealLatticeDatum p hp).logShell ⊆ Set.range ((↑) : ℚ → ℝ) := by
  intro x hx
  obtain ⟨n, hn⟩ := (sourceLogShellRealLattice_logShell_mem_iff p hp x).mp hx
  refine ⟨(n : ℚ) / (sourceLogShellStar p : ℚ), ?_⟩
  change (((n : ℚ) / (sourceLogShellStar p : ℚ) : ℚ) : ℝ) = x
  have hpstar : ((sourceLogShellStar p : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (sourceLogShellStar_pos hp.pos).ne'
  push_cast
  rw [div_eq_iff hpstar, mul_comm]
  exact hn.symm

/-- 对 ℚ-像的 span 归约：落在 `span ℚ s`（`s ⊆ ℚ` 的像）中的实数有有理值。 -/
theorem sourceLogShell_span_subset_ratCast {s : Set ℝ}
    (hs : s ⊆ Set.range ((↑) : ℚ → ℝ)) {x : ℝ}
    (hx : x ∈ Submodule.span ℚ s) : ∃ q : ℚ, (q : ℝ) = x := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs hy
  | zero => exact ⟨0, by norm_num⟩
  | add y z _ _ hy hz =>
      obtain ⟨q₁, h₁⟩ := hy
      obtain ⟨q₂, h₂⟩ := hz
      exact ⟨q₁ + q₂, by rw [Rat.cast_add, h₁, h₂]⟩
  | smul a y _ hy =>
      obtain ⟨q, hq⟩ := hy
      exact ⟨a * q, by rw [Rat.cast_mul, Rat.smul_def, hq]⟩

/-- 严格性：纤维 `IQ` 严格小于 `ℝ`（`√2 ∉ IQ`，用 `irrational_sqrt_two`）。 -/
theorem sourceLogShellRealLattice_sqrt_two_not_mem_IQSpan (p : ℕ) (hp : Nat.Prime p) :
    (Real.sqrt 2 : ℝ) ∉ (sourceLogShellRealLatticeDatum p hp).IQSpan := by
  intro hx
  obtain ⟨q, hq⟩ := sourceLogShell_span_subset_ratCast
    (sourceLogShellRealLattice_logShell_subset_ratCast p hp) hx
  exact irrational_sqrt_two ⟨q, hq⟩

/-! ## 6. 校准：双纤维同域族（`p = 2`/`p = 3`，`K = ℝ`）与包级检验 -/

theorem sourceLogShellRealLatticeTwoPlacePrime (b : Bool) :
    Nat.Prime (if b then 2 else 3) := by
  split
  · exact Nat.prime_two
  · exact Nat.prime_three

/-- 双纤维族：`b = true` 取 `p = 2`（`p* = 4`，`logShell = (1/4)ℤ`），
`b = false` 取 `p = 3`（`p* = 3`，`logShell = (1/3)ℤ`）；两纤维 `K = ℝ` 同域。 -/
noncomputable def sourceLogShellRealLatticeTwoPlaceFamily : Bool → SourceLogShellDatum :=
  fun b => sourceLogShellRealLatticeDatum (if b then 2 else 3)
    (sourceLogShellRealLatticeTwoPlacePrime b)

/-- 透传检查：族的坐标域对变量 `b` 定义等价于 `ℝ`。 -/
theorem sourceLogShellRealLatticeTwoPlaceFamily_K (b : Bool) :
    (sourceLogShellRealLatticeTwoPlaceFamily b).K = ℝ :=
  rfl

/-- 双纤维族上的规范元素：`true ↦ 1 / 4`、`false ↦ 1 / 3`（均为 `(p*_v)^{-1}` 型值）。 -/
noncomputable def sourceLogShellRealLatticeTwoPlaceElement :
    (b : Bool) → (sourceLogShellRealLatticeTwoPlaceFamily b).K :=
  fun b => if b then (1 / 4 : ℝ) else (1 / 3 : ℝ)

/-- 包级严格性检验用常值元素：两纤维均取 `√2`。 -/
noncomputable def sourceLogShellRealLatticeTwoPlaceSqrtTwoElement :
    (b : Bool) → (sourceLogShellRealLatticeTwoPlaceFamily b).K :=
  fun _ => (Real.sqrt 2 : ℝ)

/-- 双纤维逐点元素：`b = true` 处 `1/4 ∈ IQ`、`b = false` 处 `1/3 ∈ IQ`。 -/
theorem sourceLogShellRealLatticeTwoPlace_piece_mem (b : Bool) :
    sourceLogShellRealLatticeTwoPlaceElement b ∈
      (sourceLogShellRealLatticeTwoPlaceFamily b).IQSpan := by
  cases b
  · have h := sourceLogShellRealLattice_inv_pStar_mem_logShell 3 Nat.prime_three
    have h3 : sourceLogShellStar 3 = 3 := by decide
    have h3' : ((sourceLogShellStar 3 : ℝ)) = 3 := by exact_mod_cast h3
    rw [h3'] at h
    norm_num at h
    exact Submodule.subset_span h
  · have h := sourceLogShellRealLattice_inv_pStar_mem_logShell 2 Nat.prime_two
    have h2 : sourceLogShellStar 2 = 4 := by decide
    have h2' : ((sourceLogShellStar 2 : ℝ)) = 4 := by exact_mod_cast h2
    rw [h2'] at h
    norm_num at h
    exact Submodule.subset_span h

/-- 包级成员检验（非空性）：逐点元素落在直和包内。 -/
theorem sourceLogShellRealLatticeTwoPlacePacket_mem :
    sourceLogShellRealLatticeTwoPlaceElement ∈
      sourceLogShellIQDirectSumPacket sourceLogShellRealLatticeTwoPlaceFamily := by
  rw [sourceLogShellIQDirectSumPacket_mem_iff]
  intro b
  exact sourceLogShellRealLatticeTwoPlace_piece_mem b

/-- 包级严格性：常值 `√2` 不在直和包内（两个纤维的 `IQ` 均不含 `√2`）。 -/
theorem sourceLogShellRealLatticeTwoPlacePacket_sqrt_two_not_mem :
    sourceLogShellRealLatticeTwoPlaceSqrtTwoElement ∉
      sourceLogShellIQDirectSumPacket sourceLogShellRealLatticeTwoPlaceFamily := by
  intro h
  rw [sourceLogShellIQDirectSumPacket_mem_iff] at h
  exact sourceLogShellRealLattice_sqrt_two_not_mem_IQSpan 2 Nat.prime_two (h true)

/-- 直和项嵌入检验：`Pi.single true (1/4)` 落在包内（原文 direct summand 语言）。 -/
theorem sourceLogShellRealLatticeTwoPlacePacket_single_mem :
    (LinearMap.single ℚ (fun b => (sourceLogShellRealLatticeTwoPlaceFamily b).K) true
      (1 / 4 : ℝ)) ∈
      sourceLogShellIQDirectSumPacket sourceLogShellRealLatticeTwoPlaceFamily :=
  sourceLogShellIQDirectSumPacket_single_mem sourceLogShellRealLatticeTwoPlaceFamily true
    (sourceLogShellRealLatticeTwoPlace_piece_mem true)

/-- 张量包严格性（双因子）：`√2 ∉ span(∏Set)`——乘积集的 Q-span 仍含于 ℚ 像，
故张量分解的非平凡性成立（相对 `K = ℝ` 真子空间）。 -/
theorem sourceLogShellRealLatticeTensor_sqrt_two_not_mem :
    (Real.sqrt 2 : ℝ) ∉ Submodule.span ℚ
      (sourceLogShellTensorProductSet
        (fun _ : Fin 2 => (sourceLogShellRealLatticeDatum 2 Nat.prime_two).logShell)) := by
  have hsub : sourceLogShellTensorProductSet
      (fun _ : Fin 2 => (sourceLogShellRealLatticeDatum 2 Nat.prime_two).logShell) ⊆
      Set.range ((↑) : ℚ → ℝ) := by
    rintro y ⟨f, hf, rfl⟩
    obtain ⟨q₀, hq₀⟩ :=
      sourceLogShellRealLattice_logShell_subset_ratCast 2 Nat.prime_two (hf 0)
    obtain ⟨q₁, hq₁⟩ :=
      sourceLogShellRealLattice_logShell_subset_ratCast 2 Nat.prime_two (hf 1)
    refine ⟨q₀ * q₁, ?_⟩
    change ((q₀ * q₁ : ℚ) : (sourceLogShellRealLatticeDatum 2 Nat.prime_two).K) =
      ∏ α : Fin 2, f α
    have hq₀' : ((q₀ : ℚ) : (sourceLogShellRealLatticeDatum 2 Nat.prime_two).K) = f 0 :=
      hq₀
    have hq₁' : ((q₁ : ℚ) : (sourceLogShellRealLatticeDatum 2 Nat.prime_two).K) = f 1 :=
      hq₁
    rw [Rat.cast_mul, Fin.prod_univ_two, hq₀', hq₁']
  intro hx
  obtain ⟨q, hq⟩ := sourceLogShell_span_subset_ratCast hsub hx
  exact irrational_sqrt_two ⟨q, hq⟩

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：IQ 多因子张量包（义务 `IUT-II.vertical-log-kummer` 的卡-C 缺口）。 -/
def sourceLogShellIQTensorPacket : Obligation :=
  { id := "IUT-II.source-log-shell-iq-tensor-packet"
    source := "IUT III, Proposition 3.2, (ii) (text l.5740-5785); " ++
      "1-tensor/n-tensor packet definitions (l.5665-5693); " ++
      "poly-isomorphism compatibility (i) (l.5706-5739)"
    status := VerificationStatus.conditional
    note :=
      "IQ multi-factor tensor packet layer, reduced pass. Proved: the finite direct-sum " ++
        "decomposition IQ(direct sum) = pi of IQ (span_pi_eq_pi_span with zero-membership " ++
        "from the frozen zero_mem_logShell), the direct-summand embedding, fiberwise " ++
        "(p*_v)^{-1} Q-scaling compatibility, the tensor decomposition " ++
        "IQ(tensor) = span of products of IQ elements (multilinear expansion over Finset), " ++
        "the nested tensor-of-direct-sums flattening, and the conditional " ++
        "poly-isomorphism transport (piCongrRight image law for direct sums; ring-equiv " ++
        "product image law for tensors). Calibration over Q-lattice data in R: " ++
        "log-shell = (p*)^{-1} Z, IQ proper and irrationality exclusion (sqrt 2 not in " ++
        "the fiber IQ, in the two-place direct-sum packet, and in the two-factor tensor " ++
        "packet). Reductions (labeled, not substituting the paper): finite direct sum " ++
        "modeled as dependent function space (R1); tensor product of ind-topological " ++
        "modules reduced to the multiplication image in the common log-coordinate field " ++
        "(R2); poly-isomorphism reduced to a single linear/ring equivalence, with the " ++
        "image-compatibility hypothesis carried by consumers (R3); archimedean case not " ++
        "formalized (R4); the mixed packet I(A, alpha D^dash_v) and per-vQ families remain " ++
        "open cards (R5)."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.source-log-shell-carrier" ] }

end LeanFormal.IUT.Audit

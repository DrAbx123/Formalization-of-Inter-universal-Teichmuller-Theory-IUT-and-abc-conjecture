/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Rat

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# IUT-II log-shell 混合包 `I(A,αD⊢_v)`：A×ι 切片载体与链（卡-C R5 下钻件，Q-span 层缩减 pass）

本文件下钻 log-shell 载体簇的卡-C 剩余卡 5/R5（`logs/coordination/vertical-log-kummer-ordered-layer-20261016.md`
§14；`SourceLogShellIQTensorPacket.lean` 缩减点 R5）：「混合包 `I(A,αD⊢_v)`（l.5688-5693）
列入剩余卡，不形式化」。本文件在 Q-span/乘性缩减模型（卡-C R1/R2）中为混合包冻结切片载体，
并给出其与嵌套张量包的相容及三向链的集层/span 层读法。

## 原文定位（冻结）

* [IUTchIII, Proposition 3.2]（`papers/motizuki_corpus/text/Inter-universal Teichmuller
  Theory III.txt`，l.5687-5693）：混合包 `log(A,αD⊢_v) ⊆ log(AD⊢_vQ)` 由「β ∈ A\{α} 因子
  的张量积与标号 α 因子的下标 v 直和项的张量积」作为 ind-topological 子模确定。
* [IUTchIII, Proposition 3.2, (i)]（l.5706-5739）：第三 display `log(A,αD⊢_v) ~→
  log(A,αF⊢×μ_v) ~→ log(A,αF_v)`（l.5731-5737）；证明为「definitions 与引用」的直接推论。
* [IUTchIII, Proposition 3.2, (ii)]（l.5740-5785）：整结构 `I(A,αD⊢_v) ⊆ log(A,αD⊢_v)`
  （l.5749-5751）；`IQ((−))` = `I((−))` 的 Q-span（l.5781-5785）。

## 边界（如实；不得顶替原文）

* Q-span/乘性模型：α₀ 因子取 v₀-直和项集合、其余因子取全 vQ-包（直和经「存在一个 v」的
  并集读出）；张量为公共 log 坐标域内的乘积像（卡-C R1/R2）。**I 层整构造（I(A,αD⊢_v)
  作为 I 层对象）不在本文件**：其前置为卡-5（mono-analytic log-shell 载体，见
  `MonoAnalyticLogShellCompactCarrier.lean`）与 [Prop 1.2, (vi)] 的 `I ⊆ log`；本文件只给
  「log 包层」的缩减读法与具名条件下的链。
* 单腿为单一环等价（卡-D R3 缩减）；逐因子像条件作为具名冻结假设由消费者携带
  （`SourceLogShellMixedChainSupply`），不偷偷消去（`codomainKummerContained` 式纪律）。
* 切片含入嵌套包需要具名假设 `1 ∈ t α v`（原文「multiplied by ±1 保持」下的单位在
  log-shell 内；对本仓库载体这是**条件**，见校准节：ℝ-格点模型可证）。
* 本文件跨度层转运使用 Mathlib 原生 `AlgEquiv.ofRingEquiv` 构造（`ℚ` → 域）；**不 import**
  `SourceLogShellTensorLegCompletion.lean`（该件在飞：无 olean），故其 `sourceLogShellArchSignApply`
  一族不在本文件复用面内。
* 消费者：Card-APT / Ind3 的 I 层目标（经卡-C/卡-D 已有接口）；QCMP（Q-span 比较）。
  义务：`IUT-II.vertical-log-kummer`（`IUTII/Kummer/VerticalCorrespondence.lean:5` pending）。
-/

namespace LeanFormal.IUT

variable {K : Type*} [Field K] [CharZero K]

/-! ## 1. 混合包载体：A×ι 切片集合（[Prop 3.2, l.5688-5693]） -/

/-- 混合包 `log(A,αD⊢_v)` 的缩减载体（乘性模型）：α₀ 因子取 v₀-直和项、其余因子取全
vQ-包（每个其余因子经「存在一个 v」读出其直和并集）；乘积在公共 log 坐标域 `K` 内。 -/
def sourceLogShellMixedSliceSet {A ι : Type*} [Fintype A] (t : A → ι → Set K)
    (α₀ : A) (v₀ : ι) : Set K :=
  {y | ∃ f : A → K, (∀ β, β ≠ α₀ → ∃ v, f β ∈ t β v) ∧ f α₀ ∈ t α₀ v₀ ∧
    y = ∏ β, f β}

/-- 切片集合的成员展开。 -/
theorem sourceLogShellMixedSliceSet_mem_iff {A ι : Type*} [Fintype A]
    (t : A → ι → Set K) (α₀ : A) (v₀ : ι) (y : K) :
    y ∈ sourceLogShellMixedSliceSet t α₀ v₀ ↔
      ∃ f : A → K, (∀ β, β ≠ α₀ → ∃ v, f β ∈ t β v) ∧ f α₀ ∈ t α₀ v₀ ∧
        y = ∏ β, f β :=
  Iff.rfl

/-- 逐因子集包含诱导切片集合包含。 -/
theorem sourceLogShellMixedSliceSet_mono {A ι : Type*} [Fintype A]
    {t t' : A → ι → Set K} (h : ∀ α v, t α v ⊆ t' α v) (α₀ : A) (v₀ : ι) :
    sourceLogShellMixedSliceSet t α₀ v₀ ⊆ sourceLogShellMixedSliceSet t' α₀ v₀ := by
  rintro y ⟨f, hf, hfα, rfl⟩
  exact ⟨f, fun β hβ => by
      rcases hf β hβ with ⟨v, hv⟩
      exact ⟨v, h β v hv⟩,
    h α₀ v₀ hfα, rfl⟩

/-- 切片包含于嵌套张量包（原文 l.5688-5690 `log(A,αD⊢_v) ⊆ log(AD⊢_vQ)` 的集合层读出）：
具名假设为逐因子集含单位元 `1`（用于把「其余因子的全 vQ-包」中未选中的 v-坐标填 1）。 -/
theorem sourceLogShellMixedSliceSet_subset_nestedTensorProductSet {A ι : Type*}
    [Fintype A] [Fintype ι] (t : A → ι → Set K) (α₀ : A) (v₀ : ι)
    (hone : ∀ α v, (1 : K) ∈ t α v) :
    sourceLogShellMixedSliceSet t α₀ v₀ ⊆ sourceLogShellNestedTensorProductSet t := by
  rintro y ⟨f, hf, hfα, rfl⟩
  classical
  let v : A → ι := fun β => if h : β = α₀ then v₀ else (hf β h).choose
  have hvα : v α₀ = v₀ := by
    simp only [v]
    rw [dif_pos trivial]
  have hvn : ∀ β (h : β ≠ α₀), v β = (hf β h).choose := by
    intro β h
    simp only [v]
    rw [dif_neg h]
  refine ⟨fun β v' => if v' = v β then f β else 1, ?_, ?_⟩
  · intro β v'
    dsimp only
    by_cases hv : v' = v β
    · rw [if_pos hv]
      by_cases hβ : β = α₀
      · subst hβ
        rw [hvα] at hv
        rwa [hv]
      · rw [hvn β hβ] at hv
        rw [hv]
        exact (hf β hβ).choose_spec
    · rw [if_neg hv]
      exact hone β v'
  · have hprod : ∀ β, (∏ v' : ι, (if v' = v β then f β else 1)) = f β := by
      intro β
      exact Fintype.prod_ite_eq' (v β) fun _ => f β
    exact (Finset.prod_congr rfl fun β _ => hprod β).symm

/-- 切片包的 Q-span 含于嵌套张量包的 Q-span（原文 l.5688-5690 的 Q-span 读出；
具名假设 `1 ∈ t α v` 同上）。 -/
theorem sourceLogShellMixedSliceSet_span_le_nestedTensorProductSet {A ι : Type*}
    [Fintype A] [Fintype ι] (t : A → ι → Set K) (α₀ : A) (v₀ : ι)
    (hone : ∀ α v, (1 : K) ∈ t α v) :
    Submodule.span ℚ (sourceLogShellMixedSliceSet t α₀ v₀) ≤
      Submodule.span ℚ (sourceLogShellNestedTensorProductSet t) :=
  Submodule.span_mono (sourceLogShellMixedSliceSet_subset_nestedTensorProductSet t α₀ v₀ hone)

/-- 副本模型（单一 datum 的 A×ι 复制承载；卡-C R1/R2）下的消费者形状：切片包落入
IQ-嵌套包（原文 l.5688-5693 与 l.5740-5751 的缩减合读）。 -/
theorem sourceLogShellMixedSliceDatum_span_le_nestedIQSpan (D : SourceLogShellDatum)
    (hone : (1 : D.K) ∈ D.logShell) {A ι : Type*} [Fintype A] [Fintype ι]
    (α₀ : A) (v₀ : ι) :
    Submodule.span ℚ
        (sourceLogShellMixedSliceSet (fun (_ : A) (_ : ι) => D.logShell) α₀ v₀) ≤
      Submodule.span ℚ
        (sourceLogShellNestedTensorProductSet (fun (_ : A) (_ : ι) => (D.IQSpan : Set D.K))) := by
  classical
  calc Submodule.span ℚ
        (sourceLogShellMixedSliceSet (fun (_ : A) (_ : ι) => D.logShell) α₀ v₀)
      ≤ Submodule.span ℚ
          (sourceLogShellNestedTensorProductSet (fun (_ : A) (_ : ι) => D.logShell)) :=
        sourceLogShellMixedSliceSet_span_le_nestedTensorProductSet
          (fun (_ : A) (_ : ι) => D.logShell) α₀ v₀ (fun _ _ => hone)
    _ = Submodule.span ℚ
          (sourceLogShellNestedTensorProductSet (fun (_ : A) (_ : ι) => (D.IQSpan : Set D.K))) :=
        sourceLogShellNestedTensorProductSet_span_eq (fun (_ : A) (_ : ι) => D.logShell)

/-! ## 2. 环等价下的像律与 ℚ-线性转运（第三 display 的集层/span 层读法） -/

/-- 切片集合在环等价下的前向像律（定向：像落于因子像族）。 -/
theorem sourceLogShellMixedSliceSet_image_ringEquiv_subset {K' : Type*} [Field K']
    [CharZero K'] {A ι : Type*} [Fintype A] (e : K ≃+* K') (t : A → ι → Set K)
    (α₀ : A) (v₀ : ι) :
    e '' sourceLogShellMixedSliceSet t α₀ v₀ ⊆
      sourceLogShellMixedSliceSet (fun α v => e '' t α v) α₀ v₀ := by
  rintro y ⟨z, ⟨f, hf, hfα, rfl⟩, rfl⟩
  exact ⟨fun β => e (f β), fun β hβ => by
      rcases hf β hβ with ⟨v, hv⟩
      exact ⟨v, ⟨f β, hv, rfl⟩⟩,
    ⟨f α₀, hfα, rfl⟩, map_prod e f Finset.univ⟩

/-- 切片集合在环等价下的像律（等号；逆方向对 `e.symm` 用前向引理后回拉）。 -/
theorem sourceLogShellMixedSliceSet_image_ringEquiv {K' : Type*} [Field K'] [CharZero K']
    {A ι : Type*} [Fintype A] (e : K ≃+* K') (t : A → ι → Set K) (α₀ : A) (v₀ : ι) :
    e '' sourceLogShellMixedSliceSet t α₀ v₀ =
      sourceLogShellMixedSliceSet (fun α v => e '' t α v) α₀ v₀ := by
  apply le_antisymm
  · exact sourceLogShellMixedSliceSet_image_ringEquiv_subset e t α₀ v₀
  · intro y hy
    have hback : e.symm y ∈ sourceLogShellMixedSliceSet t α₀ v₀ := by
      have h1 : e.symm y ∈ sourceLogShellMixedSliceSet
          (fun α v => e.symm '' (e '' t α v)) α₀ v₀ :=
        sourceLogShellMixedSliceSet_image_ringEquiv_subset e.symm
          (fun α v => e '' t α v) α₀ v₀ ⟨y, hy, rfl⟩
      have harg : (fun α v => e.symm '' (e '' t α v)) = t := by
        funext α v
        ext z
        constructor
        · rintro ⟨w, ⟨w', hw', rfl⟩, rfl⟩
          simpa using hw'
        · intro hz
          exact ⟨e z, ⟨z, hz, rfl⟩, e.symm_apply_apply z⟩
      rwa [harg] at h1
    exact ⟨e.symm y, hback, e.apply_symm_apply y⟩

/-- 环等价作为 ℚ-线性等价的转运（Mathlib 原生 `AlgEquiv.ofRingEquiv` 于 ℚ-代数结构；
本件自足构造，不用在飞件 `SourceLogShellTensorLegCompletion` 的同名构造）。 -/
noncomputable def sourceLogShellMixedSliceRatLinearEquiv {K' : Type*} [Field K']
    [CharZero K'] (e : K ≃+* K') : K ≃ₗ[ℚ] K' :=
  (AlgEquiv.ofRingEquiv (f := e) fun c => map_ratCast e c).toLinearEquiv

/-- 上述 ℚ-线性等价的底层函数即环等价。 -/
@[simp] theorem sourceLogShellMixedSliceRatLinearEquiv_apply {K' : Type*} [Field K']
    [CharZero K'] (e : K ≃+* K') (x : K) :
    sourceLogShellMixedSliceRatLinearEquiv e x = e x :=
  AlgEquiv.ofRingEquiv_apply (fun c => map_ratCast e c) x

/-- 上述 ℚ-线性等价的底层函数即环等价（函数层；供 `Submodule.map_span` 重写）。 -/
theorem sourceLogShellMixedSliceRatLinearEquiv_coe {K' : Type*} [Field K'] [CharZero K']
    (e : K ≃+* K') :
    ((sourceLogShellMixedSliceRatLinearEquiv e).toLinearMap : K → K') = ⇑e := by
  funext x
  exact sourceLogShellMixedSliceRatLinearEquiv_apply e x

/-- 切片包的 Q-span 在环等价转运下的像律（[Prop 3.2, (i)] 第三 display 的单腿
span 层读法；目标族为因子像族）。 -/
theorem sourceLogShellMixedSliceSet_span_map_ringEquiv {K' : Type*} [Field K']
    [CharZero K'] {A ι : Type*} [Fintype A] (e : K ≃+* K') (t : A → ι → Set K)
    (α₀ : A) (v₀ : ι) :
    Submodule.map (sourceLogShellMixedSliceRatLinearEquiv e).toLinearMap
        (Submodule.span ℚ (sourceLogShellMixedSliceSet t α₀ v₀)) =
      Submodule.span ℚ
        (sourceLogShellMixedSliceSet (fun α v => e '' t α v) α₀ v₀) := by
  rw [Submodule.map_span, sourceLogShellMixedSliceRatLinearEquiv_coe,
    sourceLogShellMixedSliceSet_image_ringEquiv e t α₀ v₀]

/-- 两腿复合（第三 display 的复合 span 读法）：先 `e₁` 再 `e₂` 的转运等于复合因子像族。 -/
theorem sourceLogShellMixedSliceSet_span_map_ringEquiv_comp {K' K'' : Type*} [Field K']
    [CharZero K'] [Field K''] [CharZero K''] {A ι : Type*} [Fintype A]
    (e₁ : K ≃+* K') (e₂ : K' ≃+* K'') (t : A → ι → Set K) (α₀ : A) (v₀ : ι) :
    Submodule.map (sourceLogShellMixedSliceRatLinearEquiv e₂).toLinearMap
        (Submodule.map (sourceLogShellMixedSliceRatLinearEquiv e₁).toLinearMap
          (Submodule.span ℚ (sourceLogShellMixedSliceSet t α₀ v₀))) =
      Submodule.span ℚ
        (sourceLogShellMixedSliceSet (fun α v => e₂ '' (e₁ '' t α v)) α₀ v₀) := by
  rw [sourceLogShellMixedSliceSet_span_map_ringEquiv e₁ t α₀ v₀,
    sourceLogShellMixedSliceSet_span_map_ringEquiv e₂ (fun α v => e₁ '' t α v) α₀ v₀]

/-! ## 3. 混合包链供给（A×ι 双层指标的逐因子像条件为具名冻结假设） -/

/-- 混合包链 `log(A,αD⊢_v) ~→ log(A,αF⊢×μ_v) ~→ log(A,αF_v)`（[Prop 3.2, (i)]
l.5731-5737）的供给（Q-span 层缩减形）：两条单一环等价腿 + 逐 (α,v) 因子的像条件
（具名冻结假设；不偷偷消去）。 -/
structure SourceLogShellMixedChainSupply (K K' K'' : Type*) [Field K] [CharZero K]
    [Field K'] [CharZero K'] [Field K''] [CharZero K''] {A ι : Type*}
    (t : A → ι → Set K) (t' : A → ι → Set K') (t'' : A → ι → Set K'') where
  /-- 左腿 `log(†D⊢_v) ~→ log(†F⊢×μ_v)` 的环等价（卡-D R3 缩减：单一等价）。 -/
  leftEquiv : K ≃+* K'
  /-- 右腿 `log(†F⊢×μ_v) ~→ log(†F_v)` 的环等价。 -/
  rightEquiv : K' ≃+* K''
  /-- 左腿的逐因子像条件（A×ι 双层指标上的具名假设）。 -/
  left_factor_image : ∀ α v, leftEquiv '' t α v = t' α v
  /-- 右腿的逐因子像条件。 -/
  right_factor_image : ∀ α v, rightEquiv '' t' α v = t'' α v

namespace SourceLogShellMixedChainSupply

variable {K K' K'' : Type*} [Field K] [CharZero K] [Field K'] [CharZero K']
  [Field K''] [CharZero K''] {A ι : Type*} {t : A → ι → Set K} {t' : A → ι → Set K'}
  {t'' : A → ι → Set K''}

/-- 链的复合腿 `log(†D⊢_v) ~→ log(†F_v)`（经中间对象 `t'`）。 -/
def chainEquiv (S : SourceLogShellMixedChainSupply K K' K'' t t' t'') : K ≃+* K'' :=
  S.leftEquiv.trans S.rightEquiv

/-- 左腿的切片像律（中间包族 `t'` 显式出现）。 -/
theorem left_image_eq (S : SourceLogShellMixedChainSupply K K' K'' t t' t'')
    [Fintype A] (α₀ : A) (v₀ : ι) :
    S.leftEquiv '' sourceLogShellMixedSliceSet t α₀ v₀ =
      sourceLogShellMixedSliceSet t' α₀ v₀ := by
  have hfam : (fun α v => S.leftEquiv '' t α v) = t' :=
    funext fun α => funext fun v => S.left_factor_image α v
  rw [sourceLogShellMixedSliceSet_image_ringEquiv S.leftEquiv t α₀ v₀, hfam]

/-- 右腿的切片像律。 -/
theorem right_image_eq (S : SourceLogShellMixedChainSupply K K' K'' t t' t'')
    [Fintype A] (α₀ : A) (v₀ : ι) :
    S.rightEquiv '' sourceLogShellMixedSliceSet t' α₀ v₀ =
      sourceLogShellMixedSliceSet t'' α₀ v₀ := by
  have hfam : (fun α v => S.rightEquiv '' t' α v) = t'' :=
    funext fun α => funext fun v => S.right_factor_image α v
  rw [sourceLogShellMixedSliceSet_image_ringEquiv S.rightEquiv t' α₀ v₀, hfam]

/-- 复合腿的切片像律（原文 l.5731-5737 第三 display 的 Q-span 层读出：
`log(A,αD⊢_v) ~→ log(A,αF_v)`）。 -/
theorem chain_image_eq (S : SourceLogShellMixedChainSupply K K' K'' t t' t'')
    [Fintype A] (α₀ : A) (v₀ : ι) :
    S.chainEquiv '' sourceLogShellMixedSliceSet t α₀ v₀ =
      sourceLogShellMixedSliceSet t'' α₀ v₀ := by
  have hcomp : ⇑S.chainEquiv = ⇑S.rightEquiv ∘ ⇑S.leftEquiv := by
    funext x
    simp only [SourceLogShellMixedChainSupply.chainEquiv, RingEquiv.trans_apply,
      Function.comp_apply]
  calc S.chainEquiv '' sourceLogShellMixedSliceSet t α₀ v₀
      = (⇑S.rightEquiv ∘ ⇑S.leftEquiv) '' sourceLogShellMixedSliceSet t α₀ v₀ := by
        rw [hcomp]
    _ = ⇑S.rightEquiv '' (⇑S.leftEquiv '' sourceLogShellMixedSliceSet t α₀ v₀) :=
        Set.image_comp ⇑S.rightEquiv ⇑S.leftEquiv _
    _ = ⇑S.rightEquiv '' sourceLogShellMixedSliceSet t' α₀ v₀ := by
        rw [S.left_image_eq α₀ v₀]
    _ = sourceLogShellMixedSliceSet t'' α₀ v₀ := S.right_image_eq α₀ v₀

/-- 左腿的 span 层像律。 -/
theorem left_span_map_eq (S : SourceLogShellMixedChainSupply K K' K'' t t' t'')
    [Fintype A] (α₀ : A) (v₀ : ι) :
    Submodule.map (sourceLogShellMixedSliceRatLinearEquiv S.leftEquiv).toLinearMap
        (Submodule.span ℚ (sourceLogShellMixedSliceSet t α₀ v₀)) =
      Submodule.span ℚ (sourceLogShellMixedSliceSet t' α₀ v₀) := by
  rw [Submodule.map_span, sourceLogShellMixedSliceRatLinearEquiv_coe, S.left_image_eq α₀ v₀]

/-- 复合腿的 span 层像律（链在 Q-span 层的完整读法）。 -/
theorem chain_span_map_eq (S : SourceLogShellMixedChainSupply K K' K'' t t' t'')
    [Fintype A] (α₀ : A) (v₀ : ι) :
    Submodule.map (sourceLogShellMixedSliceRatLinearEquiv S.chainEquiv).toLinearMap
        (Submodule.span ℚ (sourceLogShellMixedSliceSet t α₀ v₀)) =
      Submodule.span ℚ (sourceLogShellMixedSliceSet t'' α₀ v₀) := by
  rw [Submodule.map_span, sourceLogShellMixedSliceRatLinearEquiv_coe, S.chain_image_eq α₀ v₀]

end SourceLogShellMixedChainSupply

/-! ## 4. 校准：ℝ-格点数据（非原文对象；检验构造与严格性） -/

/-- 校准：ℝ-格点数据上 `1 ∈ logShell`（`p*_v · 1 = p*_v ∈ preLogShell = ℤ` 的像）。 -/
theorem sourceLogShellRealLattice_one_mem_logShell (p : ℕ) (hp : Nat.Prime p) :
    (1 : ℝ) ∈ (sourceLogShellRealLatticeDatum p hp).logShell := by
  change ((sourceLogShellRealLatticeDatum p hp).pStar : ℝ) * 1 ∈
    (sourceLogShellRealLatticeDatum p hp).preLogShell
  rw [mul_one, sourceLogShellRealLattice_pStar_eq p hp,
    sourceLogShellRealLattice_preLogShell_eq p hp]
  exact ⟨(sourceLogShellStar p : ℤ), by simp⟩

/-- 校准：ℝ-格点数据上混合切片的任一元素在 ℚ-像内（每因子 logShell ⊆ ℚ-像，乘积封闭）。 -/
theorem sourceLogShellRealLatticeMixedSlice_subset_ratCast (p : ℕ) (hp : Nat.Prime p)
    {A ι : Type*} [Fintype A] (α₀ : A) (v₀ : ι) :
    sourceLogShellMixedSliceSet
        (fun (_ : A) (_ : ι) => (sourceLogShellRealLatticeDatum p hp).logShell)
        α₀ v₀ ⊆ Set.range ((↑) : ℚ → ℝ) := by
  rintro y ⟨f, hf, hfα, rfl⟩
  classical
  have hfr : ∀ β, f β ∈ Set.range ((↑) : ℚ → ℝ) := by
    intro β
    by_cases h : β = α₀
    · subst h
      exact sourceLogShellRealLattice_logShell_subset_ratCast p hp hfα
    · rcases hf β h with ⟨v, hv⟩
      exact sourceLogShellRealLattice_logShell_subset_ratCast p hp hv
  choose g hg using hfr
  refine ⟨∏ β, g β, ?_⟩
  change algebraMap ℚ ℝ (∏ β, g β) = ∏ β, f β
  rw [map_prod]
  exact Finset.prod_congr rfl fun β _ => hg β

/-- 校准严格性：切片包的 Q-span 仍不含 `√2`（张量分解对混合切片保持真子模）。 -/
theorem sourceLogShellRealLatticeMixedSlice_sqrt_two_not_mem (p : ℕ) (hp : Nat.Prime p)
    {A ι : Type*} [Fintype A] (α₀ : A) (v₀ : ι) :
    (Real.sqrt 2) ∉ Submodule.span ℚ
      (sourceLogShellMixedSliceSet
        (fun (_ : A) (_ : ι) => (sourceLogShellRealLatticeDatum p hp).logShell) α₀ v₀) := by
  intro hx
  obtain ⟨q, hq⟩ := sourceLogShell_span_subset_ratCast
    (sourceLogShellRealLatticeMixedSlice_subset_ratCast p hp α₀ v₀) hx
  exact irrational_sqrt_two ⟨q, hq⟩

/-- 校准非平凡见证：`(p*_v)^{-1}` 幂落在切片包内（非空、且由单位幂给出）。 -/
theorem sourceLogShellRealLatticeMixedSlice_inv_pStar_pow_mem (p : ℕ) (hp : Nat.Prime p)
    {A ι : Type*} [Fintype A] (α₀ : A) (v₀ : ι) :
    ((sourceLogShellStar p : ℝ))⁻¹ ^ Fintype.card A ∈
      sourceLogShellMixedSliceSet
        (fun (_ : A) (_ : ι) => (sourceLogShellRealLatticeDatum p hp).logShell) α₀ v₀ := by
  refine ⟨fun _ => ((sourceLogShellStar p : ℝ))⁻¹, ?_, ?_, ?_⟩
  · intro _ _
    exact ⟨v₀, sourceLogShellRealLattice_inv_pStar_mem_logShell p hp⟩
  · exact sourceLogShellRealLattice_inv_pStar_mem_logShell p hp
  · rw [Finset.prod_const]
    rfl

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：混合包 `I(A,αD⊢_v)` 的 Q-span 层切片载体与链（卡-C 剩余卡 5/R5 下钻件）。 -/
def sourceLogShellMixedPacket : Obligation :=
  { id := "IUT-II.source-log-shell-mixed-packet"
    source := "IUT III, Proposition 3.2 (text l.5687-5693, l.5706-5739, l.5740-5785)"
    status := VerificationStatus.conditional
    note :=
      "Mixed-packet slice carrier, Q-span layer, reduced pass. Proved: the A x iota " ++
        "slice set (v0-summand for the alpha0 factor, full vQ packs for the other " ++
        "factors), monotonicity, inclusion into the nested tensor packet under the " ++
        "named unit-membership hypothesis 1 in t (l.5688-5690), the ring-equivalence " ++
        "image law and its span-map law plus two-leg composite, the mixed chain " ++
        "supply (factorwise image conditions as named frozen fields) with left/right/" ++
        "chain image equalities and left/chain span-map laws, and the real-lattice " ++
        "calibration (1 in logShell, slice subset of the rational image, sqrt 2 " ++
        "excluded from the slice span, unit-power witness). Transport is Mathlib-native " ++
        "(AlgEquiv.ofRingEquiv); the in-flight SourceLogShellTensorLegCompletion is not " ++
        "imported. Reductions (card-C R1/R2 multiplicative common-field model; card-D " ++
        "R3 single ring-equivalence legs; factorwise image conditions carried by " ++
        "consumers). The I-layer whole construction I(A, alpha D_v) remains gated on " ++
        "card-5 (mono-analytic log-shell compact carrier) and Prop 1.2(vi) I subset log; " ++
        "arch case not formalized."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.source-log-shell-iq-tensor-packet" ] }

end LeanFormal.IUT.Audit

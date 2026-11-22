/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActionCompatibility
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.Module.Rat

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# IUT-II log-shell 张量腿补全：arch 因子内 {±1}-独立轨道（R9-ii）与 A-包 Q-span 链腿（R9-iii）

本文件续 `logs/coordination/vertical-log-kummer-ordered-layer-20261016.md` §23.5 登记的
R9 剩余卡：(ii) arch 因子内 {±1}-独立轨道（R8 卡的群结构/作用层部分，R8 载体层维持
PARK）；(iii) A-包 Q-span 层链腿。R9-(i)（`⊗` 本体）维持精确卡（报告 §24.3）。
消费者：Ind3（张量包 Q-span 读回、上半相容）、QCMP（Q-span / log-volume 比较）、
Card-APT；义务 `IUT-II.vertical-log-kummer`（`IUTII/Kummer/VerticalCorrespondence.lean:5`
pending）。

## 原文定位（冻结）

* [IUTchIII, Definition 1.1, (ii)]（`papers/motizuki_corpus/text/Inter-universal
  Teichmuller Theory III.txt`，arch 情形 l.1367-1511）：pre-log-shell（l.1474-1480)；
  log-shell 定义为「被乘 ±1 保持（preserved by multiplication by ±1）、端点在
  `Ψ∼_{†F_v} ↠ Ψgp_{†F_v}` 核生成元相差下唯一确定的闭线段」的 `Ψ×_log`-轨道
  （l.1480-1506）。本文件 §1.1 的闭线段载体即该闭线段的 ℚ-模缩减模型（±1-保持、
  生成元唯一到 ±1）；`Ψ×_log`-轨道与 Ψcns 载体不在树内（缩减点 A-1，PARK 维持）。
* [IUTchIII, Proposition 1.2, (vii)]（l.1950-1999）：arch poly-isomorphism =
  「an orbit of isomorphisms with respect to the independent actions of {±1} on each
  of the direct factors that occur in the construction of [AbsTopIII], Proposition
  5.8, (v)」（l.1971-1973、l.1982-1984）；末句（l.1997-1999）与 respective log-shells
  及角/径向 log-volumes 相容。本文件 §1.2 的「直因子族 `(A → ℤˣ)` 的逐坐标独立
  符号作用 + 作用轨道」即该机制的缩减模型。
* [IUTchIII, Proposition 3.2, (i)]（l.5706-5739）：Prop 1.2(vi)(vii) 的 poly-isomorphism
  诱导张量包 poly-isomorphism `log(αD⊢_vQ) ~→ log(αF⊢×μ_vQ) ~→ log(αF_vQ)` 及
  A-包 `log(AD⊢_vQ) ~→ log(AF⊢×μ_vQ) ~→ log(AF_vQ)`（l.5716-5730）。本文件 §2 为
  Q-span 层链腿（具名假设下；缩减点 B-1/B-2）。
* Meitner §16 G5（`logs/coordination/wild-brainstorm-20261017.md` §16，l.501-525；
  引用 `III.pagewise.plain` 行号体系）：arch 归一化两层 = packet（p_v / e 常数层，
  μlog(O)=0 零点）+ procession（对 j ∈ F⋇_l 平均）；两层均为常数层操作，不破坏
  ±1-不变性。本文件 §1.3 的下降引理与 procession 平均引理为该输入的接口形
  （readout 层；报告 §24.6）。

## 缩减点（显式标注；不得顶替原命题）

* A-1（(ii) 腿载体层）。闭线段以 ℚ-模模型 `{t • a | t ∈ [-1,1]}` 承载；`Ψ∼` 的
  拓扑结构、「端点相差核生成元、唯一确定」中的满射 `Ψ∼ ↠ Ψgp` 与核、`Ψ×_log`-轨道
  均不在树内（R8 卡阻断 1、2 维持 PARK，Hilbert 更正口径）；本件只做闭线段 ±1-保持、
  生成元唯一与直因子独立符号作用的群结构/作用层（阻断 3 的缩减解除）。
* A-2（(ii) 腿语义）。「multiplication by ±1」以 `ℤˣ` 经 zsmul 在 ℚ-模上承载（加性
  记号下的 ±1-作用）；poly-isomorphism 缩为单一同构的符号轨道（继承卡-D R3）。
* B-1（(iii) 腿）。链腿取环等价（卡-D R2/R3 缩减：乘法模型、单腿非 poly）；张量包
  对象为公共 log 坐标域 `K` 内的乘积像集（卡-C §4），`⊗` 本体见 (i) 卡。
* B-2（(iii) 腿）。Q-span 层结论在 ℚ-线性等价（环等价诱导，`map_ratCast`）下陈述；
  ind-topological 模结构不形式化。
* G5（§1.3）。procession 平均以有限指标集上的 `Finset.sum` 形承载；`F⋇_l` 标签集与
  权重（N_v 乘积）不形式化；packet 归一化常数层不形式化。

## 与相邻件的区分（只读对照，不 import）

* R9-(i) `⊗` 本体：不在本件；精确卡见报告 §24.3。
* 卡-C `SourceLogShellIQTensorPacket.lean` §4：本件 §2 在其 span 分解事实与
  `sourceLogShell_prod_image_ringEquiv` 之上接链腿，不修改其声明。
* 冻结件 `SourceLogShellActionCompatibility.lean`：本件复用其 §3 的
  `sourceLogShellDependentTensorSet` 与 `sourceLogShellDependentTensorSet_image_map`。
* Hilbert 线 `MonoAnalyticLogShellFormalLogMul.lean`（在飞）：仅接口层（同报告 §23.6），
  不 import、不重复。
-/

namespace LeanFormal.IUT

/-! ## 1. R9-(ii)：arch 因子内 {±1}-独立轨道（缩减 pass） -/

/-! ### 1.1 闭线段载体与 ±1-保持（[IUTchIII, Def 1.1, (ii), l.1480-1506]） -/

section ArchSegmentBasic

variable {K : Type*} [AddCommGroup K] [Module ℚ K]

/-- arch 直因子的闭线段载体（缩减点 A-1）：`{t • a | t ∈ [-1,1]}`——被乘 ±1 保持、
端点为 `±a` 的闭线段的 ℚ-模模型（[IUTchIII, Def 1.1, (ii)]）。 -/
def sourceLogShellArchSegment (a : K) : Set K :=
  {x | ∃ t : ℚ, t ∈ Set.Icc (-1) 1 ∧ x = t • a}

/-- 生成元在闭线段内（端点之一）。 -/
theorem sourceLogShellArchSegment_self_mem (a : K) :
    a ∈ sourceLogShellArchSegment a :=
  ⟨1, ⟨by norm_num, by norm_num⟩, (one_smul ℚ a).symm⟩

/-- 另一端点在闭线段内。 -/
theorem sourceLogShellArchSegment_neg_mem (a : K) :
    -a ∈ sourceLogShellArchSegment a :=
  ⟨-1, ⟨by norm_num, by norm_num⟩, (neg_one_smul ℚ a).symm⟩

/-- 闭线段被乘 ±1 保持（原文 l.1484、l.1493「preserved by multiplication by ±1」）。 -/
theorem sourceLogShellArchSegment_neg_image (a : K) :
    (fun x : K => -x) '' sourceLogShellArchSegment a = sourceLogShellArchSegment a := by
  ext x
  constructor
  · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by rw [neg_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(-t) • a, ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩,
      by simp only [neg_smul, neg_neg]⟩

/-- 闭线段在缩放下的像律：`c • seg a = seg (c • a)`。 -/
theorem sourceLogShellArchSegment_smul_image (c : ℚ) (a : K) :
    (fun x : K => c • x) '' sourceLogShellArchSegment a =
      sourceLogShellArchSegment (c • a) := by
  ext x
  constructor
  · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, by rw [smul_comm]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t • a, ⟨t, ht, rfl⟩, by rw [smul_comm]⟩

/-- `seg (-a) = seg a`（闭线段只依赖生成元到 ±1）。 -/
theorem sourceLogShellArchSegment_neg_gen (a : K) :
    sourceLogShellArchSegment (-a) = sourceLogShellArchSegment a := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by rw [smul_neg, neg_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by rw [smul_neg, neg_smul, neg_neg]⟩

/-- `{±1}`（以 `ℤˣ` 承载）保持闭线段（原文 l.1484、l.1493 的 `±1`-保持的群形）。 -/
theorem sourceLogShellArchSegment_units_image (s : ℤˣ) (a : K) :
    (fun x : K => (s : ℤ) • x) '' sourceLogShellArchSegment a =
      sourceLogShellArchSegment a := by
  rcases Int.units_eq_one_or s with h | h
  · rw [h]
    have hfun : (fun x : K => ((1 : ℤˣ) : ℤ) • x) = id := by
      funext x
      simp only [Units.val_one, one_zsmul]
      rfl
    rw [hfun, Set.image_id]
  · rw [h]
    have hfun : (fun x : K => ((-1 : ℤˣ) : ℤ) • x) = fun x : K => -x := by
      funext x
      simp only [Units.val_neg, Units.val_one, neg_one_zsmul]
    rw [hfun, sourceLogShellArchSegment_neg_image]

end ArchSegmentBasic

section ArchSegmentUnique

variable {K : Type*} [Field K] [CharZero K]

/-- 符号配对辅助：`s, t ∈ [-1, 1]` 且 `s * t = 1` ⇒ `(s, t) = (1, 1)` 或 `(-1, -1)`。 -/
theorem sourceLogShell_rat_mul_eq_one_of_mem_Icc {s t : ℚ}
    (hs : s ∈ Set.Icc (-1) 1) (ht : t ∈ Set.Icc (-1) 1) (hst : s * t = 1) :
    (s = 1 ∧ t = 1) ∨ (s = -1 ∧ t = -1) := by
  have hle : s + t ≤ 2 := by
    have h : 0 ≤ (1 - s) * (1 - t) := mul_nonneg (by linarith [hs.2]) (by linarith [ht.2])
    nlinarith [h, hst]
  have hge : -2 ≤ s + t := by
    have h : 0 ≤ (1 + s) * (1 + t) := mul_nonneg (by linarith [hs.1]) (by linarith [ht.1])
    nlinarith [h, hst]
  have hb : (s + t) ^ 2 ≤ 4 := by
    have h : 0 ≤ (2 - (s + t)) * (2 + (s + t)) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h]
  have hzero : (s - t) ^ 2 = 0 := by
    have hsq : (s - t) ^ 2 = (s + t) ^ 2 - 4 * (s * t) := by ring
    nlinarith [hsq, hb, hst, sq_nonneg (s - t)]
  have hst_eq : s = t := by
    have h := (sq_eq_zero_iff.mp hzero : s - t = 0)
    linarith
  have hs2 : s ^ 2 = 1 := by simpa [pow_two, hst_eq] using hst
  rcases sq_eq_one_iff.mp hs2 with hs1 | hs1
  · left
    refine ⟨hs1, ?_⟩
    rw [hs1] at hst
    simpa using hst
  · right
    refine ⟨hs1, ?_⟩
    rw [hs1] at hst
    linarith

/-- 生成元唯一到 ±1（原文 l.1482、l.1491「the uniquely determined closed line segment
… preserved by multiplication by ±1」的缩减读数）：`a ≠ 0` 时闭线段确定其生成元到 ±1。 -/
theorem sourceLogShellArchSegment_eq_iff {a b : K} (ha : a ≠ 0) :
    sourceLogShellArchSegment a = sourceLogShellArchSegment b ↔ b = a ∨ b = -a := by
  constructor
  · intro h
    have hb_in : b ∈ sourceLogShellArchSegment a := by
      rw [h]
      exact sourceLogShellArchSegment_self_mem b
    have ha_in : a ∈ sourceLogShellArchSegment b := by
      rw [← h]
      exact sourceLogShellArchSegment_self_mem a
    obtain ⟨s, hs, hbs⟩ := hb_in
    obtain ⟨t, ht, hat⟩ := ha_in
    have hb0 : b ≠ 0 := by
      intro hb
      apply ha
      rw [hat, hb, smul_zero]
    have hb_eq : b = (s * t) • b := by
      calc b = s • a := hbs
        _ = s • (t • b) := by rw [hat]
        _ = (s * t) • b := by rw [smul_smul]
    have hst : s * t = 1 := by
      have h1 : (s * t) • b = (1 : ℚ) • b := by
        rw [← hb_eq, one_smul]
      have h1' : ((s * t : ℚ) : K) * b = ((1 : ℚ) : K) * b := by
        simpa [Rat.smul_def] using h1
      exact Rat.cast_injective (mul_right_cancel₀ hb0 h1')
    rcases sourceLogShell_rat_mul_eq_one_of_mem_Icc hs ht hst with ⟨hs1, _⟩ | ⟨hs1, _⟩
    · left
      rw [hbs, hs1, one_smul]
    · right
      rw [hbs, hs1, neg_one_smul]
  · rintro (rfl | rfl)
    · rfl
    · exact (sourceLogShellArchSegment_neg_gen a).symm

end ArchSegmentUnique

/-! ### 1.2 直因子族上的独立符号作用与轨道（[IUTchIII, Prop 1.2, (vii), l.1971-1984]） -/

section ArchSignAction

variable {A : Type*}

/-- 直因子族上 {±1} 的逐坐标独立符号作用（原文 l.1971-1973、l.1982-1984
「independent actions of {±1} on each of the direct factors」的缩减模型）：
`s : A → ℤˣ` 为每个直因子各自的符号选择；坐标为 `(s α : ℤ) • x α`（`K` 显式参数，
与 `sourceLogShellDependentTensorSet` 的约定一致，避免依赖族实例元变量的悬置）。 -/
def sourceLogShellArchSignApply (K : A → Type*) [∀ α, AddCommGroup (K α)]
    (s : A → ℤˣ) (x : (α : A) → K α) : (α : A) → K α :=
  fun α => (s α : ℤ) • x α

/-- 单位符号作用为恒等。 -/
theorem sourceLogShellArchSignApply_one (K : A → Type*) [∀ α, AddCommGroup (K α)] :
    sourceLogShellArchSignApply K (1 : A → ℤˣ) = id := by
  funext x α
  change ((1 : A → ℤˣ) α : ℤ) • x α = x α
  rw [Pi.one_apply, Units.val_one, one_zsmul]

/-- 符号作用复合律（逐坐标乘法）。 -/
theorem sourceLogShellArchSignApply_mul (K : A → Type*) [∀ α, AddCommGroup (K α)]
    (s t : A → ℤˣ) :
    sourceLogShellArchSignApply K (s * t) =
      sourceLogShellArchSignApply K s ∘ sourceLogShellArchSignApply K t := by
  funext x α
  change (((s * t) α : ℤˣ) : ℤ) • x α = (s α : ℤ) • ((t α : ℤ) • x α)
  rw [Pi.mul_apply, Units.val_mul, mul_zsmul]

/-- 逆符号作用为左逆。 -/
theorem sourceLogShellArchSignApply_inv_comp (K : A → Type*) [∀ α, AddCommGroup (K α)]
    (s : A → ℤˣ) :
    sourceLogShellArchSignApply K s⁻¹ ∘ sourceLogShellArchSignApply K s = id := by
  rw [← sourceLogShellArchSignApply_mul K, inv_mul_cancel, sourceLogShellArchSignApply_one K]

/-- 逆符号作用为右逆。 -/
theorem sourceLogShellArchSignApply_comp_inv (K : A → Type*) [∀ α, AddCommGroup (K α)]
    (s : A → ℤˣ) :
    sourceLogShellArchSignApply K s ∘ sourceLogShellArchSignApply K s⁻¹ = id := by
  rw [← sourceLogShellArchSignApply_mul K, mul_inv_cancel, sourceLogShellArchSignApply_one K]

/-- 每个符号选择给出同构（「orbit of isomorphisms」的缩减：每个轨道元素为双射）。 -/
theorem sourceLogShellArchSignApply_bijective (K : A → Type*) [∀ α, AddCommGroup (K α)]
    (s : A → ℤˣ) :
    Function.Bijective (sourceLogShellArchSignApply K s) :=
  ⟨Function.LeftInverse.injective fun x => congrFun (sourceLogShellArchSignApply_inv_comp K s) x,
    Function.RightInverse.surjective fun y =>
      congrFun (sourceLogShellArchSignApply_comp_inv K s) y⟩

/-- 独立符号作用保持逐因子符号稳定的依赖族张量包集（与 log-shell 内容相容的作用层；
复用卡-D §3 的 `sourceLogShellDependentTensorSet_image_map`）。 -/
theorem sourceLogShellArchSignApply_image_dependentTensorSet (K : A → Type*)
    [∀ α, AddCommGroup (K α)] (s : A → ℤˣ) (t : ∀ α, Set (K α))
    (ht : ∀ α, (fun y : K α => (s α : ℤ) • y) '' t α = t α) :
    sourceLogShellArchSignApply K s '' sourceLogShellDependentTensorSet K t =
      sourceLogShellDependentTensorSet K t := by
  have h : (fun α => (fun y : K α => (s α : ℤ) • y) '' t α) = t := funext ht
  calc sourceLogShellArchSignApply K s '' sourceLogShellDependentTensorSet K t
      = sourceLogShellDependentTensorSet K
          (fun α => (fun y : K α => (s α : ℤ) • y) '' t α) :=
        sourceLogShellDependentTensorSet_image_map
          (fun α => fun y : K α => (s α : ℤ) • y) t
    _ = sourceLogShellDependentTensorSet K t := by rw [h]

/-- 独立符号作用轨道（poly-isomorphism 的缩减模型：单一同构的符号选择轨道）。 -/
def sourceLogShellArchSignOrbit (K : A → Type*) [∀ α, AddCommGroup (K α)]
    (x : (α : A) → K α) : Set ((α : A) → K α) :=
  {y | ∃ s : A → ℤˣ, y = sourceLogShellArchSignApply K s x}

/-- 每个符号作用的像在轨道内。 -/
theorem sourceLogShellArchSignOrbit_mem_apply (K : A → Type*) [∀ α, AddCommGroup (K α)]
    (s : A → ℤˣ) (x : (α : A) → K α) :
    sourceLogShellArchSignApply K s x ∈ sourceLogShellArchSignOrbit K x :=
  ⟨s, rfl⟩

/-- 轨道闭合（两段符号选择可合成一段）。 -/
theorem sourceLogShellArchSignOrbit_trans (K : A → Type*) [∀ α, AddCommGroup (K α)]
    {x y z : (α : A) → K α}
    (hy : y ∈ sourceLogShellArchSignOrbit K x) (hz : z ∈ sourceLogShellArchSignOrbit K y) :
    z ∈ sourceLogShellArchSignOrbit K x := by
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨t, rfl⟩ := hz
  exact ⟨t * s, (congrFun (sourceLogShellArchSignApply_mul K t s) x).symm⟩

/-- 轨道落入符号稳定的张量包集（「compatible with the respective log-shells」的作用层：
若每因子集被符号作用保持且 `x` 在其内，则轨道全在其内）。 -/
theorem sourceLogShellArchSignOrbit_subset_of_factor_stable (K : A → Type*)
    [∀ α, AddCommGroup (K α)] {x : (α : A) → K α} {t : ∀ α, Set (K α)}
    (hx : x ∈ sourceLogShellDependentTensorSet K t)
    (ht : ∀ (α : A) (s : ℤˣ), (fun y : K α => (s : ℤ) • y) '' t α = t α) :
    sourceLogShellArchSignOrbit K x ⊆ sourceLogShellDependentTensorSet K t := by
  rintro y ⟨s, rfl⟩
  have h := sourceLogShellArchSignApply_image_dependentTensorSet K s t (fun α => ht α (s α))
  exact h ▸ ⟨x, hx, rfl⟩

/-- 符号不变读出（log-volume 缩减形）在轨道上不变（「compatible with the respective …
log-volumes」的下降形）。 -/
theorem sourceLogShellArchSignOrbit_readout_eq (K : A → Type*) [∀ α, AddCommGroup (K α)]
    {vol : ((α : A) → K α) → ℝ}
    (hvol : ∀ (s : A → ℤˣ) (x), vol (sourceLogShellArchSignApply K s x) = vol x)
    {x y : (α : A) → K α} (hy : y ∈ sourceLogShellArchSignOrbit K x) :
    vol y = vol x := by
  obtain ⟨s, rfl⟩ := hy
  exact hvol s x

/-- procession 平均（有限标签集上的归一化读出；Meitner §16 G5）保持符号不变性：
各标签读出符号不变 ⇒ 平均读出在符号轨道上不变。 -/
theorem sourceLogShellArchSignOrbit_processionAverage_eq (K : A → Type*) [∀ α, AddCommGroup (K α)]
    {ι : Type*} [Fintype ι]
    (vol : ι → ((α : A) → K α) → ℝ)
    (hvol : ∀ (j : ι) (s : A → ℤˣ) (x), vol j (sourceLogShellArchSignApply K s x) = vol j x)
    (s : A → ℤˣ) (x : (α : A) → K α) :
    ∑ j, vol j (sourceLogShellArchSignApply K s x) = ∑ j, vol j x :=
  Finset.sum_congr rfl fun j _ => hvol j s x

end ArchSignAction

/-! ### 1.3 逐因子闭线段张量包上的符号作用（arch 实例化） -/

section ArchSegmentTensor

variable {A : Type*}

/-- 逐因子闭线段的依赖族张量包（arch 因子独立并置的载体形；Def 1.1(ii) 的线段在
direct factor 族上的并置）。 -/
def sourceLogShellArchSegmentTensorSet (K : A → Type*) [∀ α, AddCommGroup (K α)]
    [∀ α, Module ℚ (K α)] (a : ∀ α, K α) : Set ((α : A) → K α) :=
  sourceLogShellDependentTensorSet K (fun α => sourceLogShellArchSegment (a α))

/-- 独立符号作用保持 arch 线段张量包（每因子线段被 ±1 保持 + 作用层像律）。 -/
theorem sourceLogShellArchSegmentTensorSet_sign_image (K : A → Type*)
    [∀ α, AddCommGroup (K α)] [∀ α, Module ℚ (K α)] (a : ∀ α, K α) (s : A → ℤˣ) :
    sourceLogShellArchSignApply K s '' sourceLogShellArchSegmentTensorSet K a =
      sourceLogShellArchSegmentTensorSet K a :=
  sourceLogShellArchSignApply_image_dependentTensorSet K s
    (fun α => sourceLogShellArchSegment (a α))
    (fun α => sourceLogShellArchSegment_units_image (s α) (a α))

/-- 线段张量包内的点，其符号轨道落在包内（poly-isomorphism 轨道对 log-shell 内容的
相容性的 arch 线段形）。 -/
theorem sourceLogShellArchSegmentTensorSet_orbit_subset (K : A → Type*)
    [∀ α, AddCommGroup (K α)] [∀ α, Module ℚ (K α)] (a : ∀ α, K α)
    {x : (α : A) → K α} (hx : x ∈ sourceLogShellArchSegmentTensorSet K a) :
    sourceLogShellArchSignOrbit K x ⊆ sourceLogShellArchSegmentTensorSet K a :=
  sourceLogShellArchSignOrbit_subset_of_factor_stable K hx
    (fun α s => sourceLogShellArchSegment_units_image s (a α))

end ArchSegmentTensor

/-! ## 2. R9-(iii)：A-包 Q-span 层链腿（[IUTchIII, Prop 3.2, (i), l.5706-5739]） -/

section IQSpanLeg

variable {K K' : Type*} [Field K] [CharZero K] [Field K'] [CharZero K']

/-- 环等价作为 ℚ-线性等价（CharZero 域上环同态固定 ℚ，`map_ratCast`）：R9-(iii)
Q-span 腿的线性承载。 -/
def sourceLogShellRingEquivRatLinearEquiv (e : K ≃+* K') : K ≃ₗ[ℚ] K' where
  toFun := e
  invFun := e.symm
  left_inv x := e.left_inv x
  right_inv x := e.right_inv x
  map_add' x y := e.map_add x y
  map_smul' c x := by
    have hc := map_ratCast e c
    rw [Rat.smul_def, Rat.smul_def, map_mul, hc]
    simp

/-- 上述 ℚ-线性等价与环等价同函数。 -/
@[simp] theorem sourceLogShellRingEquivRatLinearEquiv_apply (e : K ≃+* K') (x : K) :
    sourceLogShellRingEquivRatLinearEquiv e x = e x := rfl

/-- 上述 ℚ-线性等价的底层函数即环等价。 -/
theorem sourceLogShellRingEquivRatLinearEquiv_coe (e : K ≃+* K') :
    ((sourceLogShellRingEquivRatLinearEquiv e).toLinearMap : K → K') = ⇑e := rfl

/-- A-包 Q-span 层链腿（单腿；[IUTchIII, Prop 3.2, (i)] 的 A-包 display 在缩减载体上的
Q-span 读出）：环等价把张量包的 Q-span 送到因子像张量包的 Q-span。 -/
theorem sourceLogShellIQTensorPacket_span_map_ringEquiv (e : K ≃+* K') {A : Type*}
    [Fintype A] (t : A → Set K) :
    Submodule.map (sourceLogShellRingEquivRatLinearEquiv e).toLinearMap
        (Submodule.span ℚ (sourceLogShellTensorProductSet t)) =
      Submodule.span ℚ (sourceLogShellTensorProductSet (fun α => e '' t α)) := by
  rw [Submodule.map_span, sourceLogShellRingEquivRatLinearEquiv_coe,
    sourceLogShell_prod_image_ringEquiv e t]

/-- A-包 Q-span 层链腿（复合形；链 `AD⊢ → AF⊢×μ → AF` 的两腿复合）。 -/
theorem sourceLogShellIQTensorPacket_span_map_ringEquiv_comp {K'' : Type*} [Field K'']
    [CharZero K''] (e₁ : K ≃+* K') (e₂ : K' ≃+* K'') {A : Type*} [Fintype A]
    (t : A → Set K) :
    Submodule.map (sourceLogShellRingEquivRatLinearEquiv e₂).toLinearMap
        (Submodule.map (sourceLogShellRingEquivRatLinearEquiv e₁).toLinearMap
          (Submodule.span ℚ (sourceLogShellTensorProductSet t))) =
      Submodule.span ℚ (sourceLogShellTensorProductSet (fun α => e₂ '' (e₁ '' t α))) := by
  rw [sourceLogShellIQTensorPacket_span_map_ringEquiv e₁ t,
    sourceLogShellIQTensorPacket_span_map_ringEquiv e₂ (fun α => e₁ '' t α)]

/-- 嵌套张量包（`⨂_α ⨁_v`）在环等价下的像律。 -/
theorem sourceLogShellNestedTensorProductSet_image_ringEquiv (e : K ≃+* K') {A : Type*}
    {ι : Type*} [Fintype A] [Fintype ι] (t : A → ι → Set K) :
    e '' sourceLogShellNestedTensorProductSet t =
      sourceLogShellNestedTensorProductSet (fun α v => e '' t α v) := by
  calc e '' sourceLogShellNestedTensorProductSet t
      = e '' sourceLogShellTensorProductSet (fun p : A × ι => t p.1 p.2) := by
        rw [sourceLogShellNestedTensorProductSet_eq_flatten]
    _ = sourceLogShellTensorProductSet (fun p : A × ι => e '' t p.1 p.2) :=
        sourceLogShell_prod_image_ringEquiv e (fun p : A × ι => t p.1 p.2)
    _ = sourceLogShellNestedTensorProductSet (fun α v => e '' t α v) :=
        (sourceLogShellNestedTensorProductSet_eq_flatten (fun α v => e '' t α v)).symm

/-- 嵌套张量包的 Q-span 层链腿（`⨂_α ⨁_v` 形）。 -/
theorem sourceLogShellNestedTensorProductSet_span_map_ringEquiv (e : K ≃+* K') {A : Type*}
    {ι : Type*} [Fintype A] [Fintype ι] (t : A → ι → Set K) :
    Submodule.map (sourceLogShellRingEquivRatLinearEquiv e).toLinearMap
        (Submodule.span ℚ (sourceLogShellNestedTensorProductSet t)) =
      Submodule.span ℚ (sourceLogShellNestedTensorProductSet (fun α v => e '' t α v)) := by
  rw [Submodule.map_span, sourceLogShellRingEquivRatLinearEquiv_coe,
    sourceLogShellNestedTensorProductSet_image_ringEquiv e t]

end IQSpanLeg

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：R9 剩余腿补全（arch 因子内 {±1}-独立轨道与 A-包 Q-span 链腿），
义务 `IUT-II.vertical-log-kummer` 的 R9 下钻件（缩减 pass）。 -/
def sourceLogShellTensorLegCompletion : Obligation :=
  { id := "IUT-II.source-log-shell-tensor-leg-completion"
    source := "IUT III, Definition 1.1, (ii) (text l.1367-1511); " ++
      "Proposition 1.2, (vii) (l.1950-1999); Proposition 3.2, (i) (l.5706-5739)"
    status := VerificationStatus.conditional
    note :=
      "R9 remaining legs, reduced pass. (ii) arch factor-internal independent " ++
        "{±1}-orbit layer: closed-segment carrier (sign-preserving, generator " ++
        "unique up to ±1), per-factor independent sign apply with group laws, " ++
        "bijectivity, dependent-tensor-set stability, orbit transitivity, " ++
        "orbit-subset stability, sign-invariant readout descent and " ++
        "procession-average invariance. (iii) A-packet Q-span chain leg: " ++
        "span-map under ring-equivalence-induced Q-linear transport, two-leg " ++
        "composite, nested form. Reductions (labeled): A-1 segment as Q-module " ++
        "model (Psi-cns carrier and Psi-times-log orbit remain PARK); A-2 {±1} " ++
        "via Z-units zsmul, single-isomorphism sign orbit (reduction R3 " ++
        "inherited); B-1 ring-equivalence legs (card-D R2/R3); B-2 Q-span layer " ++
        "only. (i) unit: tensor-product proper not formalized (precise card in " ++
        "report section 24.3)."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.source-log-shell-action-compatibility" ] }

end LeanFormal.IUT.Audit

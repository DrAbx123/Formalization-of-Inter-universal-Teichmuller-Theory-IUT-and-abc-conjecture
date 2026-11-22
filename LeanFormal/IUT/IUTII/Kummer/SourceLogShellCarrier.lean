/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummerOrderedLayer
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# IUT-II log-shell 载体层最小构造（缩减 pass）

本文件对位仓库义务 `IUT-II.vertical-log-kummer`（`IUTII/Kummer/VerticalCorrespondence.lean`
l.5 的 pending 记录：「The lower polynomial/root kernel is available ... The paper's
vertical log-Kummer correspondence, its Frobenioid input, and all compatibility laws
are still pending.」）下的「log-shell 载体」缺口：`I = (p*_v)^{-1} · log_v(O^×_{Kv})`
的对象与基本律。消费者：Card-APT（平行移动不变量）、Ind3（上半相容）、QCMP
（log-volume / `Q`-span 比较）。上游接口：`IUTII/Kummer/VerticalLogKummerOrderedLayer.lean`
的冻结结构 `NonarchimedeanLogKummerUpperSemi`（只读 import）。

## 原文定位（冻结；沿用任务①报告的定位方式）

* [IUTchIII, Definition 1.1, (i)]（`papers/motizuki_corpus/text/Inter-universal
  Teichmuller Theory III.txt`，l.1264-1277、l.1330-1351）：`pre-log-shell` 是
  `G_v(†Π_v)`-不变的 `Ψ×_{†F_v}` 子幺半群在 `Ψ~_{†F_v}` 中的像，构成紧拓扑模；
  `p*_v := p_v`（`p_v` 奇）、`p*_v := p_v²`（`p_v` 偶）；`log-shell` `I_{†F_v}`
  是「`pre-log-shell` 乘以因子 `(p*_v)^{-1}`」的结果。
* [IUTchIII, 引言, l.208-215]：`I_v = p_v^{-1} · log_v(O^×_{Kv}) ⊆ K_v ⊆ F_v`
  （「roughly speaking」）；[l.220-226]：`O^⊿_{Kv} ⊆ I_v`，`log_v(O^×_{Kv}) ⊆ I_v`——
  `I_v` 同时包含 log-link 定义域与值域两侧的 Kummer 同构的像
  （[IUTchIII, Proposition 1.2, (v)]；[Remark 1.2.2, (i)]）。
* [IUTchIII, Definition 1.1, (ii)]（l.1474-1506）：arch 情形 `pre-log-shell` 是单位
  `Ψ×_{†F_v}` 决定的紧拓扑子商；`log-shell` 是闭线段之 `Ψ×_{log}`-轨道。
  本文件不形式化 arch 情形（保留为未证卡）。
* [IUTchIII, Definition 1.1, (iii)]（l.1528-1546）：`log(†F) = {log(†F_v) := Ψ~}`
  的加法（ind-topological 模）结构；`v ∈ V^non` 处带 `G_v(†Π_v)`-作用。
* [IUTchII, Example 1.8, (ix)]（`...Theory II.txt` l.2359-2366）：`G ≅ G_k` 时
  `I(G) ⊆ O^×μ(G)` 是「`p^{-1}` 乘以 `G`-不变 `O^×(G)` 在 `O^×μ(G)` 中的像」；
  由此得 multiradial 环境的「log-shell 版本」。
* [IUTchIII, Proposition 3.2, (ii)]（l.5769-5785）：log-shell 的闭单位球作为
  `log(...)` 上的整结构；`IQ((−))` 定义为 `I((−))` 的 `Q`-span（并对
  `D⊢/F/F⊢×μ` 各版本同用）。

## 缩减点（显式标注；不得顶替原命题）

1. 「ind-topological 域」`Ψ~_{†F_v}` 缩减为其 log 坐标所在的域 `K`
   （保留域结构、`(p*_v)^{-1}` 因子与乘法记号；ind/拓扑/紧性结构不形式化）。
2. `G_v(†Π_v)` 作用不显式，直接以其不变量子幺半群 `invariants` 为数据
   （原文定义 1.1, (i) 的输入之一即该不变量子幺半群）。
3. Mathlib v4.32.2 无 `p` 进 log，取合同参数 `logMap : Units →* Multiplicative K`
   （保留原文使用的 `log(uv) = log u + log v` 与 `log 1 = 0` 两条律）。
4. 定义域侧 Kummer 像 `O^⊿ ⊆ I` 由 `invariants` 的像承载（定理
   `invariant_unitLog_mem_logShell`，可证）；值域侧 `log(O^×) ⊆ I` 在缩减载体上
   不由结构推出（原文依赖 `O^×` 的 `p`-幂封闭性等分析事实），作为具名条件
   `codomainKummerContained` 由消费者显式携带。
5. arch 情形（定义 1.1, (ii)）与「紧拓扑模/子商」的拓扑陈述不形式化。
-/

namespace LeanFormal.IUT

universe u

/-! ## 0. `p*_v` 因子（[IUTchIII, Definition 1.1, (i), l.1336-1343]） -/

/-- `p*_v := p_v`（`p_v` 奇）；`p*_v := p_v²`（`p_v` 偶）。原文：
「Write p*_v := p_v when p_v is odd and p*_v := p_v² when p_v is even.」 -/
def sourceLogShellStar (p : ℕ) : ℕ := if p % 2 = 1 then p else p * p

theorem sourceLogShellStar_pos {p : ℕ} (hp : 0 < p) : 0 < sourceLogShellStar p := by
  unfold sourceLogShellStar
  split
  · exact hp
  · positivity

/-! ## 1. log-shell 载体（[IUTchIII, Definition 1.1, (i)] 的缩减核） -/

set_option linter.checkUnivs false in
/-- log-shell 载体数据（缩减 pass）。字段逐条对应原文：

* `p`/`hp`：剩余特征 `p_v`；
* `K`：`Ψ~_{†F_v}` 的 log 坐标域（「ind-topological 域」的缩减，缩减点 1）；
* `Units`：`Ψ×_{†F_v}`（单位子幺半群所属的单位群；原文 `Ψ× ⊆ Ψ`）；
* `invariants`：`G_v(†Π_v)`-不变子幺半群（缩减点 2）；
* `logMap`：`p` 进 log（缩减点 3）。

`pStar` 由 `p` 派生（原文 `p*_v` 的定义即由 `p_v` 给出）。 -/
structure SourceLogShellDatum where
  p : ℕ
  hp : Nat.Prime p
  K : Type u
  [fieldK : Field K]
  [charZeroK : CharZero K]
  Units : Type u
  [groupUnits : CommGroup Units]
  invariants : Submonoid Units
  logMap : Units →* Multiplicative K

attribute [instance] SourceLogShellDatum.fieldK SourceLogShellDatum.charZeroK
  SourceLogShellDatum.groupUnits

namespace SourceLogShellDatum

/-- `p*_v`（[IUTchIII, Definition 1.1, (i)]）。 -/
def pStar (D : SourceLogShellDatum) : ℕ := sourceLogShellStar D.p

theorem pStar_pos (D : SourceLogShellDatum) : 0 < D.pStar :=
  sourceLogShellStar_pos D.hp.pos

theorem pStar_ne_zero (D : SourceLogShellDatum) : D.pStar ≠ 0 :=
  D.pStar_pos.ne'

theorem pStar_ne_zero_cast (D : SourceLogShellDatum) : (D.pStar : D.K) ≠ 0 := by
  intro h
  exact D.pStar_ne_zero (by exact_mod_cast h : D.pStar = 0)

/-- `pre-log-shell`：`G_v(†Π_v)`-不变单位子幺半群在 `Ψ~_{†F_v}` 中的像
（[IUTchIII, Definition 1.1, (i), l.1330-1336]；`Ψ~` 在此以其 log 坐标域 `K` 出现，
缩减点 1、3）。 -/
def preLogShell (D : SourceLogShellDatum) : Set D.K :=
  {a | ∃ u ∈ D.invariants, (D.logMap u).toAdd = a}

/-- `log-shell` `I_{†F_v}`：`pre-log-shell` 乘以因子 `(p*_v)^{-1}` 的结果
（[IUTchIII, Definition 1.1, (i), l.1344-1351]）；即
`a ∈ I ↔ p*_v · a ∈ pre-log-shell`。 -/
def logShell (D : SourceLogShellDatum) : Set D.K :=
  {a | (D.pStar : D.K) * a ∈ D.preLogShell}

/-- 单位层（`Ψ×_{†F_v}` 的全部单位在 `log` 下的像；[IUTchIII, Definition 1.1, (ii),
l.1474-1479] 的子商与 [IUTchII, Example 1.8, (ix)] 的值域侧像的缩减载体）。 -/
def unitLayer (D : SourceLogShellDatum) : Set D.K :=
  {a | ∃ u : D.Units, (D.logMap u).toAdd = a}

/-- 值域侧 Kummer 含入 `log_v(O^×_{Kv}) ⊆ I_v`（[IUTchIII, 引言, l.223-224]；
[Proposition 1.2, (v)]）的具名条件（缩减点 4）。 -/
def codomainKummerContained (D : SourceLogShellDatum) : Prop :=
  D.unitLayer ⊆ D.logShell

/-- 单位层：`log 1 = 0` 落在 pre-log-shell（不变量子幺半群含 `1`）。 -/
theorem zero_mem_preLogShell (D : SourceLogShellDatum) : (0 : D.K) ∈ D.preLogShell := by
  refine ⟨1, D.invariants.one_mem, ?_⟩
  rw [map_one, toAdd_one]

/-- 乘性：pre-log-shell 是不变量子幺半群在 `log` 下的像，故（在 log 坐标下）
对源乘法封闭，即对加法封闭。 -/
theorem add_mem_preLogShell (D : SourceLogShellDatum) {x y : D.K}
    (hx : x ∈ D.preLogShell) (hy : y ∈ D.preLogShell) :
    x + y ∈ D.preLogShell := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨u * v, D.invariants.mul_mem hu hv, ?_⟩
  rw [map_mul, toAdd_mul]

theorem logMap_pow_val (D : SourceLogShellDatum) (u : D.Units) (n : ℕ) :
    (D.logMap (u ^ n)).toAdd = n • (D.logMap u).toAdd := by
  rw [map_pow, toAdd_pow]

theorem pow_smul_mem_preLogShell (D : SourceLogShellDatum) {u : D.Units}
    (hu : u ∈ D.invariants) (n : ℕ) :
    n • (D.logMap u).toAdd ∈ D.preLogShell :=
  ⟨u ^ n, D.invariants.pow_mem hu n, D.logMap_pow_val u n⟩

/-- `pre-log-shell ⊆ log-shell`：不变量子幺半群对 `p*_v` 次幂封闭，故
`p*_v · log(u) = log(u^{p*_v})` 仍在 pre-log-shell 内
（[IUTchIII, Definition 1.1, (i)] 的 `(p*_v)^{-1}` 因子律；对应
[IUTchIII, 引言, l.221-224] 的 `O^⊿ ⊆ I`）。 -/
theorem preLogShell_subset_logShell (D : SourceLogShellDatum) :
    D.preLogShell ⊆ D.logShell := by
  rintro a ⟨u, hu, rfl⟩
  show (D.pStar : D.K) * (D.logMap u).toAdd ∈ D.preLogShell
  rw [← nsmul_eq_mul]
  exact D.pow_smul_mem_preLogShell hu D.pStar

theorem preLogShell_subset_unitLayer (D : SourceLogShellDatum) :
    D.preLogShell ⊆ D.unitLayer :=
  fun _ ⟨u, _, h⟩ => ⟨u, h⟩

theorem invariant_unitLog_mem_preLogShell (D : SourceLogShellDatum) {u : D.Units}
    (hu : u ∈ D.invariants) : (D.logMap u).toAdd ∈ D.preLogShell :=
  ⟨u, hu, rfl⟩

/-- 定义域侧 Kummer 像含入（`O^⊿ ⊆ I` 的缩减形状）：不变量单位的像落在 log-shell
（可证，无需附加条件）。 -/
theorem invariant_unitLog_mem_logShell (D : SourceLogShellDatum) {u : D.Units}
    (hu : u ∈ D.invariants) : (D.logMap u).toAdd ∈ D.logShell :=
  D.preLogShell_subset_logShell (D.invariant_unitLog_mem_preLogShell hu)

theorem zero_mem_logShell (D : SourceLogShellDatum) : (0 : D.K) ∈ D.logShell :=
  D.preLogShell_subset_logShell D.zero_mem_preLogShell

/-- log-shell 对加法封闭（pre-log-shell 对加法封闭，再乘 `p*_v`）。 -/
theorem add_mem_logShell (D : SourceLogShellDatum) {x y : D.K}
    (hx : x ∈ D.logShell) (hy : y ∈ D.logShell) : x + y ∈ D.logShell := by
  show (D.pStar : D.K) * (x + y) ∈ D.preLogShell
  rw [mul_add]
  exact D.add_mem_preLogShell hx hy

theorem codomainKummerContained_iff (D : SourceLogShellDatum) :
    D.codomainKummerContained ↔
      ∀ u : D.Units, (D.logMap u).toAdd ∈ D.logShell := by
  constructor
  · intro h u
    exact h ⟨u, rfl⟩
  · rintro h a ⟨u, rfl⟩
    exact h u

/-- [IUTchIII, 引言, l.220-226]：`I_v` 同时包含 log-link 定义域
（`O^⊿`，第一支，可证）与值域（`log(O^×)`，第二支，具名条件）两侧的
Kummer 同构的像。 -/
theorem kummerImages_mem_logShell (D : SourceLogShellDatum)
    (h : D.codomainKummerContained) :
    (∀ u ∈ D.invariants, (D.logMap u).toAdd ∈ D.logShell) ∧
      (∀ u : D.Units, (D.logMap u).toAdd ∈ D.logShell) :=
  ⟨fun _ hu => D.invariant_unitLog_mem_logShell hu, fun u => h ⟨u, rfl⟩⟩

/-- 把 pre-log-shell 逐元素乘以因子 `(p*_v)^{-1}` 得到的集合
（[IUTchIII, Definition 1.1, (i), l.1344-1346]：「the result of multiplying the
pre-log-shell by the factor (p*_v)^{-1}」的集合论形状）。 -/
def invScaledPreLogShell (D : SourceLogShellDatum) : Set D.K :=
  {b | ∃ x ∈ D.preLogShell, (D.pStar : D.K)⁻¹ * x = b}

/-- [IUTchIII, Definition 1.1, (i), l.1344-1346] 的等式形式：
`I = (p*_v)^{-1} · pre-log-shell`。 -/
theorem logShell_eq_invScaledPreLogShell (D : SourceLogShellDatum) :
    D.logShell = D.invScaledPreLogShell := by
  ext b
  constructor
  · intro hb
    exact ⟨(D.pStar : D.K) * b, hb, by
      rw [← mul_assoc, inv_mul_cancel₀ D.pStar_ne_zero_cast, one_mul]⟩
  · rintro ⟨x, hx, rfl⟩
    show (D.pStar : D.K) * ((D.pStar : D.K)⁻¹ * x) ∈ D.preLogShell
    rw [← mul_assoc, mul_inv_cancel₀ D.pStar_ne_zero_cast, one_mul]
    exact hx

/-! ## 2. `I^Q`：log-shell 的 `Q`-span（[IUTchIII, Proposition 3.2, (ii), l.5781-5785]） -/

/-- `IQ((−))`：`I((−))` 的 `Q`-span（原文「we shall denote by "IQ((−))" the
`Q`-span of "I((−))"」）。`K` 为 `CharZero` 域，`Q`-span 直接取 `Submodule.span ℚ`。 -/
def IQSpan (D : SourceLogShellDatum) : Submodule ℚ D.K :=
  Submodule.span ℚ D.logShell

theorem logShell_subset_IQSpan (D : SourceLogShellDatum) :
    D.logShell ⊆ D.IQSpan :=
  Submodule.subset_span

theorem preLogShell_subset_IQSpan (D : SourceLogShellDatum) :
    D.preLogShell ⊆ D.IQSpan :=
  fun _ ha => D.logShell_subset_IQSpan (D.preLogShell_subset_logShell ha)

theorem zero_mem_IQSpan (D : SourceLogShellDatum) : (0 : D.K) ∈ D.IQSpan :=
  D.logShell_subset_IQSpan D.zero_mem_logShell

/-- `Q`-标量与 `K`-乘法的桥：`Rat.cast ((p*_v : ℚ)^{-1}) = (p*_v : K)^{-1}`。 -/
theorem pStar_inv_cast (D : SourceLogShellDatum) :
    Rat.cast ((D.pStar : ℚ)⁻¹) = (D.pStar : D.K)⁻¹ := by
  rw [Rat.cast_inv, Rat.cast_natCast]

/-- 因子 `(p*_v)^{-1}` 的 `Q`-缩放把 log-shell 映入 `IQ`
（log-shell 的乘性因子在 `IQ` 层不改变 span 值域）。 -/
theorem pStar_inv_mul_mem_IQSpan (D : SourceLogShellDatum) {x : D.K}
    (hx : x ∈ D.logShell) : (D.pStar : D.K)⁻¹ * x ∈ D.IQSpan := by
  have h : ((D.pStar : ℚ)⁻¹) • x ∈ D.IQSpan :=
    D.IQSpan.smul_mem ((D.pStar : ℚ)⁻¹) (D.logShell_subset_IQSpan hx)
  rw [Rat.smul_def, pStar_inv_cast] at h
  exact h

/-- `IQ` 等于 pre-log-shell 的 `Q`-span（差一个 `Q`-单位缩放 `(p*_v)^{-1}`）。 -/
theorem IQSpan_eq_span_preLogShell (D : SourceLogShellDatum) :
    D.IQSpan = Submodule.span ℚ D.preLogShell := by
  unfold IQSpan
  apply le_antisymm
  · rw [Submodule.span_le]
    intro a ha
    have hpre : (D.pStar : D.K) * a ∈ D.preLogShell := ha
    have h1 : ((D.pStar : ℚ)⁻¹) • ((D.pStar : D.K) * a) ∈
        Submodule.span ℚ D.preLogShell :=
      (Submodule.span ℚ D.preLogShell).smul_mem ((D.pStar : ℚ)⁻¹)
        (Submodule.subset_span hpre)
    have h2 : ((D.pStar : ℚ)⁻¹) • ((D.pStar : D.K) * a) = a := by
      rw [Rat.smul_def, pStar_inv_cast, ← mul_assoc,
        inv_mul_cancel₀ D.pStar_ne_zero_cast, one_mul]
    rw [h2] at h1
    exact h1
  · rw [Submodule.span_le]
    exact fun _ ha => Submodule.subset_span (D.preLogShell_subset_logShell ha)

/-! ## 3. 与冻结接口的相容（消费者路径：Card-APT、Ind3、QCMP） -/

/-- 由载体与值域侧 Kummer 含入条件组装任务①的冻结结构
`NonarchimedeanLogKummerUpperSemi`（[IUTchIII, Proposition 3.5, (ii), (a)] 的接口形状）。
缩减：log-link 步在缩减载体上取恒等对应（本载体不携带级别结构）。 -/
def toNonarchimedeanUpperSemi (D : SourceLogShellDatum) (h : D.codomainKummerContained) :
    NonarchimedeanLogKummerUpperSemi where
  Unit := fun _ => D.Units
  coricModule := D.K
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

/-- 把 log-shell 的任一测量上界沿冻结接口推给全部 Kummer 像（复用
[IUT-II.vertical-log-kummer-ordered-layer] 的 `logShell_images_bounded`；
消费者：Cor 3.12 的 log-volume 上界、Card-APT 的平行移动不变量）。 -/
theorem codomain_kummerImages_bounded (D : SourceLogShellDatum)
    (h : D.codomainKummerContained) (measure : D.K → ℝ) {hull : ℝ}
    (hshell : ∀ d, d ∈ D.logShell → measure d ≤ hull) :
    (∀ (_m : ℤ) (u : D.Units), measure ((D.logMap u).toAdd) ≤ hull) ∧
      (∀ {m m' : ℤ} (u w : D.Units), w = u → m < m' →
        measure ((D.logMap w).toAdd) ≤ hull) :=
  (D.toNonarchimedeanUpperSemi h).logShell_images_bounded measure hshell

/-! ## 4. span 并集律（张量包/直和的 `Q`-span 分解形状，[IUTchIII, l.582-587] 下游用法） -/

theorem sourceLogShell_span_union {K : Type u} [Field K] [CharZero K] (s t : Set K) :
    Submodule.span ℚ (s ∪ t) = Submodule.span ℚ s ⊔ Submodule.span ℚ t :=
  Submodule.span_union s t

end SourceLogShellDatum

namespace VerticalLogKummerOrderedLayer

variable (L : VerticalLogKummerOrderedLayer)

/-- Card-APT 形状的消费定理：若有序层各级的 Kummer 像经载体的 `logMap` 因子化
（`hfactor`），则沿 log-link 迭代（平行移动）的全部像都落在 log-shell 的任一
上界之下。 -/
theorem hullDominates_of_sourceLogShell {D : SourceLogShellDatum}
    (h : D.codomainKummerContained) (φ : ∀ m : ℕ, L.F m → D.Units)
    (measure : D.K → L.D)
    (hfactor : ∀ (m : ℕ) (x : L.F m), L.kummer m x = measure ((D.logMap (φ m x)).toAdd))
    {hull : L.D} (hmeasure : ∀ a ∈ D.logShell, measure a ≤ hull) (x₀ : L.F 0) :
    L.HullDominates x₀ hull := by
  intro n
  rw [hfactor]
  exact hmeasure _ (h ⟨φ (0 + n) (L.transport 0 n x₀), rfl⟩)

end VerticalLogKummerOrderedLayer

/-! ## 5. 校准模型（非空性检验与因子非平凡性；标注为校准，非原文对象） -/

/-- 校准用 log：`v₂`（乘性到加性）。校准模型取 `p = 2`、`K = ℚ`，用于检验载体
与基本律非空，且 `(p*_v)^{-1}` 因子真的改变集合。 -/
def sourceLogShellCalibrationLogMap : ℚˣ →* Multiplicative ℚ where
  toFun u := Multiplicative.ofAdd ((padicValRat 2 (u : ℚ) : ℤ) : ℚ)
  map_one' := by
    simp
  map_mul' u v := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← ofAdd_add]
    congr 1
    rw [Units.val_mul, padicValRat.mul (Units.ne_zero u) (Units.ne_zero v)]
    push_cast
    ring

/-- 校准载体：`p = 2`、`K = ℚ`、`Units = ℚˣ`、不变量取全部单位（校准简化）、
`log = v₂`；`p*_v = p*_2 = 4`。 -/
def sourceLogShellCalibrationDatum : SourceLogShellDatum where
  p := 2
  hp := Nat.prime_two
  K := ℚ
  Units := ℚˣ
  invariants := ⊤
  logMap := sourceLogShellCalibrationLogMap

theorem sourceLogShellCalibration_pStar_eq : sourceLogShellCalibrationDatum.pStar = 4 :=
  by decide

theorem sourceLogShellCalibrationLogMap_apply (u : ℚˣ) :
    (sourceLogShellCalibrationLogMap u).toAdd = ((padicValRat 2 (u : ℚ) : ℤ) : ℚ) := by
  simp [sourceLogShellCalibrationLogMap, toAdd_ofAdd]

theorem sourceLogShellCalibration_four_eq :
    (sourceLogShellCalibrationLogMap (Units.mk0 (4 : ℚ) (by norm_num))).toAdd = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [sourceLogShellCalibrationLogMap_apply, Units.val_mk0]
  have h4 : (4 : ℚ) = ((2 : ℕ) : ℚ) ^ 2 := by norm_num
  rw [h4, padicValRat.pow, padicValRat.self (by norm_num : 1 < 2)]
  norm_num

/-- 校准：`2 = v₂(4) ∈ pre-log-shell`。 -/
theorem sourceLogShellCalibration_two_mem_preLogShell :
    (2 : ℚ) ∈ sourceLogShellCalibrationDatum.preLogShell :=
  ⟨Units.mk0 (4 : ℚ) (by norm_num), Submonoid.mem_top _,
    sourceLogShellCalibration_four_eq⟩

/-- 校准：`1/2 = (p*_2)^{-1} · 2 ∈ log-shell`（`(p*_v)^{-1}` 因子作用后的新元素）。 -/
theorem sourceLogShellCalibration_half_mem_logShell :
    (1 / 2 : ℚ) ∈ sourceLogShellCalibrationDatum.logShell := by
  show (sourceLogShellCalibrationDatum.pStar : ℚ) * (1 / 2) ∈
    sourceLogShellCalibrationDatum.preLogShell
  rw [sourceLogShellCalibration_pStar_eq]
  norm_num
  exact sourceLogShellCalibration_two_mem_preLogShell

/-- 校准：`1/2 ∉ pre-log-shell`（`v₂` 像落在 `ℤ` 内；因子确实改变集合）。 -/
theorem sourceLogShellCalibration_half_not_mem_preLogShell :
    (1 / 2 : ℚ) ∉ sourceLogShellCalibrationDatum.preLogShell := by
  rintro ⟨u, -, hu⟩
  let v : ℚˣ := u
  have h0 : ((padicValRat 2 (v : ℚ) : ℤ) : ℚ) = 1 / 2 := by
    rw [← sourceLogShellCalibrationLogMap_apply v]
    exact hu
  have h1 : (2 : ℚ) * ((padicValRat 2 (v : ℚ) : ℤ) : ℚ) = 1 := by
    rw [h0]
    norm_num
  have h2 : (2 * padicValRat 2 (v : ℚ) : ℤ) = 1 := by
    have h3 : ((2 * padicValRat 2 (v : ℚ) : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
      push_cast
      exact h1
    exact_mod_cast h3
  omega

/-- 校准：因子非平凡——`1/2 ∈ I` 而 `1/2 ∉ pre-log-shell`。 -/
theorem sourceLogShellCalibration_factor_nontrivial :
    (1 / 2 : ℚ) ∈ sourceLogShellCalibrationDatum.logShell ∧
      (1 / 2 : ℚ) ∉ sourceLogShellCalibrationDatum.preLogShell :=
  ⟨sourceLogShellCalibration_half_mem_logShell,
    sourceLogShellCalibration_half_not_mem_preLogShell⟩

/-- 校准：值域侧含入条件在 `invariants = ⊤` 时成立（`p*_2 = 4` 倍幂封闭）。 -/
theorem sourceLogShellCalibration_codomainKummerContained :
    sourceLogShellCalibrationDatum.codomainKummerContained := by
  intro a ha
  rw [SourceLogShellDatum.unitLayer, Set.mem_setOf_eq] at ha
  obtain ⟨u, rfl⟩ := ha
  rw [SourceLogShellDatum.logShell, Set.mem_setOf_eq]
  rw [sourceLogShellCalibration_pStar_eq]
  refine ⟨u ^ 4, Submonoid.mem_top _, ?_⟩
  rw [SourceLogShellDatum.logMap_pow_val]
  exact nsmul_eq_mul 4 _

/-- 校准模型不经任何假设即落在冻结接口上（非空性）。 -/
def sourceLogShellCalibrationUpperSemi : NonarchimedeanLogKummerUpperSemi :=
  sourceLogShellCalibrationDatum.toNonarchimedeanUpperSemi
    sourceLogShellCalibration_codomainKummerContained

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：log-shell 载体层（义务 `IUT-II.vertical-log-kummer` 的载体缺口）。 -/
def sourceLogShellCarrier : Obligation :=
  { id := "IUT-II.source-log-shell-carrier"
    source := "IUT III, Definition 1.1, (i) (text l.1264-1351); Introduction l.208-226; " ++
      "IUT II, Example 1.8, (ix) (text l.2359-2366); IUT III, Proposition 3.2, (ii) (l.5769-5785)"
    status := VerificationStatus.conditional
    note :=
      "Log-shell carrier layer, reduced pass. Proved from the explicit source-facing " ++
        "fields: pre-log-shell = image of the invariant submonoid under logMap; " ++
        "log-shell = (p*_v)^{-1} * pre-log-shell with p*_v from Definition 1.1, (i); " ++
        "multiplicativity (add_mem_preLogShell), unit layer (zero_mem_preLogShell, " ++
        "zero_mem_logShell), preLogShell_subset_logShell (locally proved O^⊿ ⊆ I), " ++
        "logShell_eq_inv_smul_preLogShell, the Q-span object IQSpan with " ++
        "IQSpan_eq_span_preLogShell and the pStar^{-1} Q-scaling law, the assembly " ++
        "toNonarchimedeanUpperSemi into the frozen ordered-layer interface, and the " ++
        "calibration model over Q with v_2 (nonvacuity and nontriviality of the " ++
        "(p*_v)^{-1} factor). Reductions (labeled, not substituting the paper): " ++
        "the ind-topological field is reduced to its log-coordinate field K; the " ++
        "G_v(†Π_v)-action is data of its invariant submonoid; the p-adic logarithm " ++
        "is a contract homomorphism (Mathlib v4.32.2 has no p-adic log); the " ++
        "codomain-side containment log(O^×) ⊆ I is the named condition " ++
        "codomainKummerContained (the paper derives it from the analysis of O^× " ++
        "p-powers); the archimedean case (Definition 1.1, (ii)) and all compactness/" ++
        "topology statements are not formalized."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.vertical-log-kummer-ordered-layer" ] }

end LeanFormal.IUT.Audit

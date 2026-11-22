/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Complex.Basic

/-!
# 探针：mono-analytic log-shell / 紧拓扑模载体的题面形状（2026-10-16）

本文件是「mono-analytic log-shell / 紧拓扑模载体 API 缺位」主问题的候选路线探针，
缺口语境见 `logs/coordination/vertical-log-kummer-ordered-layer-20261016.md` 的
§14（卡-B、缩减点 1）、§18/§19（PARKED 4/5）与
`logs/coordination/monoanalytic-logshell-exploration-20261016.md` 的路线清单。

目标：在现有 Mathlib v4.32.2 上验证下列题面形状可以**直接陈述并证明**：

1. 紧 Hausdorff 载体上连续标量作用（`ContinuousSMul`）的紧性保持（紧集之积-作用像仍紧）；
2. 连续像/标量缩放像在 T2 载体中既紧又闭（`I = (p*_v)^{-1} · log(O^×)` 的载体形状）；
3. `ℤ`-模侧（交换拓扑群）：`ℤ`-缩放像紧/闭、紧商群、子模拓扑闭包闭且紧；
4. `ℚ`-模侧的条件形状：`ℚ`-轨道闭包紧、`ℚ`-标量像紧；
5. 具体载体：`ℤ_[p]`（含 `p`-倍乘像）、`ℚ_[p]` 与 `ℂ` 的闭球紧性可用。

本探针**不**声称：(a) 原文 `I(αD⊢_vQ) ⊆ log(αD⊢_vQ)` 已证；(b) ind-拓扑域 `Ψ~`、
`p` 进 `log`、Galois 作用层已建；(c) 本文件已接入任何生产 import 图。上述题面形状的
可证性只说明「紧拓扑模 API 在现有 Mathlib 上可陈述可证」这一工程结论，不构成对
[IUTchIII, Prop 1.2(vi)] 或 [AbsTopIII] 层桥接的数学完成声明。
-/

open scoped Pointwise

namespace LeanFormal.IUT

/-! ## 1. 一般紧拓扑模形状（任意标量环/群 `R`） -/

section GeneralSmul

variable {R M : Type*}

/-- log-shell 形状（标量像）：紧标量集与紧模子集的积-作用像仍紧。
对位 `I = (p*_v)^{-1} • log(O^×)`：`p*_v^{-1}` 单点紧、`log` 像紧 ⇒ 缩放像紧。 -/
theorem compactSmulSet_isCompact [SMul R M] [TopologicalSpace R] [TopologicalSpace M]
    [ContinuousSMul R M] {K : Set R} {S : Set M} (hK : IsCompact K) (hS : IsCompact S) :
    IsCompact (K • S) :=
  hK.smul_set hS

/-- 单因子缩放像：连续模映射的紧像经标量 `c` 缩放后仍紧。
即原文 `I` 层「不变单位像 ⇒ 乘 `(p*_v)^{-1}`」两步保持紧性。 -/
theorem invScaledImage_isCompact [SMul R M] [TopologicalSpace R] [TopologicalSpace M]
    [ContinuousSMul R M] {U : Type*} [TopologicalSpace U] {f : U → M} {S : Set U}
    (c : R) (hf : Continuous f) (hS : IsCompact S) :
    IsCompact (c • (f '' S)) := by
  simpa only [Set.singleton_smul] using isCompact_singleton.smul_set (hS.image hf)

end GeneralSmul

/-- 紧 Hausdorff 载体上的「闭像」形状：连续映射把紧载体的闭集映成闭集
（闭 ⇒ 紧 ⇒ 紧像 ⇒ T2 中闭）。pre-log-shell 作为闭集像的载体形状。 -/
theorem continuous_image_isClosed_of_compactSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {f : X → Y} (hf : Continuous f)
    {s : Set X} (hs : IsClosed s) :
    IsClosed (f '' s) :=
  (hs.isCompact.image hf).isClosed

/-! ## 2. ℤ-模侧（交换拓扑群 = 紧拓扑 ℤ-模） -/

section ZModule

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- `ℤ`-缩放像紧：`n • ·` 连续（`ContinuousSMul ℤ` 自动实例），紧域上像紧。
对位 `p ℤ_p`、`p ℤ_[p]` 一类整子模的载体形状。 -/
theorem zsmul_range_isCompact [CompactSpace M] (n : ℤ) :
    IsCompact (Set.range fun x : M => n • x) :=
  isCompact_range (continuous_const_smul n)

/-- `ℤ`-缩放像在 T2 中闭：紧 + T2 ⇒ 闭（`pℤ_p` 是闭子模的载体形状）。 -/
theorem zsmul_range_isClosed [CompactSpace M] [T2Space M] (n : ℤ) :
    IsClosed (Set.range fun x : M => n • x) :=
  (zsmul_range_isCompact n).isClosed

end ZModule

/-- 紧交换拓扑群的商仍紧（`QuotientAddGroup` 实例，`ℤ`-模右侧商形状；
例如 `ℤ_[p] ⧸ pℤ_[p] ≅ 𝔽_p` 的紧性载体）。 -/
example {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] (H : AddSubgroup G) : CompactSpace (G ⧸ H) :=
  inferInstance

/-- 子模拓扑闭包：闭（定义）+ 在紧载体中紧。`IQ` 一类 `ℚ`-span 的闭包承载形状。 -/
theorem submodule_topologicalClosure_isClosed_isCompact {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [TopologicalSpace R] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] [CompactSpace M] (S : Submodule R M) :
    IsClosed (S.topologicalClosure : Set M) ∧ IsCompact (S.topologicalClosure : Set M) :=
  ⟨S.isClosed_topologicalClosure, S.isClosed_topologicalClosure.isCompact⟩

/-! ## 3. ℚ-模侧（条件形状：`Module ℚ` + 相容连续作用） -/

/-- `ℚ`-轨道闭包紧：紧载体中任意闭集紧（不变单位子群的闭包像形状；
该步只用 `SMul ℚ` 与紧性，不需要作用连续性）。 -/
theorem ratOrbit_closure_isCompact {V : Type*} [SMul ℚ V] [TopologicalSpace V] [CompactSpace V]
    (v : V) :
    IsCompact (closure (Set.range fun q : ℚ => q • v)) :=
  isClosed_closure.isCompact

section RatModule

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℚ V] [CompactSpace V]

omit [IsTopologicalAddGroup V] [CompactSpace V] in
/-- `ℚ`-标量像：紧标量集 × 紧子集的作用像紧（`ℚ`-span 的有限部件载体形状）。 -/
theorem ratSmulSet_isCompact {K : Set ℚ} {S : Set V} (hK : IsCompact K) (hS : IsCompact S) :
    IsCompact (K • S) :=
  hK.smul_set hS

end RatModule

/-! ## 4. 具体紧载体（非空性证据，非原文对象） -/

section PadicCarriers

variable (p : ℕ) [Fact p.Prime]

/-- `ℤ_[p]` 是紧 Hausdorff 拓扑交换环（`PadicInt.compactSpace`）。 -/
example : CompactSpace ℤ_[p] := inferInstance

/-- `ℤ` 在 `ℤ_[p]` 上的作用连续（拓扑交换群自动实例）。 -/
example : ContinuousSMul ℤ ℤ_[p] := inferInstance

/-- `ℤ_[p]` 在自身上的环作用连续（`ContinuousMul` 自动实例）。 -/
example : ContinuousSMul ℤ_[p] ℤ_[p] := inferInstance

/-- `pℤ_[p]`（`p`-倍乘像）紧：极大理想/开紧子模的载体形状。 -/
theorem padicInt_mulPrime_range_isCompact :
    IsCompact (Set.range fun x : ℤ_[p] => x * (p : ℤ_[p])) :=
  isCompact_range (continuous_id.mul continuous_const)

/-- `pℤ_[p]` 闭：紧 + T2。 -/
theorem padicInt_mulPrime_range_isClosed :
    IsClosed (Set.range fun x : ℤ_[p] => x * (p : ℤ_[p])) :=
  (padicInt_mulPrime_range_isCompact p).isClosed

/-- `ℚ_[p]` 的任意闭球紧（`ProperSpace ℚ_[p]`）：非 arch 半径球载体。 -/
theorem padic_closedBall_isCompact (z : ℚ_[p]) (r : ℝ) :
    IsCompact (Metric.closedBall z r) :=
  isCompact_closedBall z r

end PadicCarriers

/-- `ℂ` 的任意闭球紧（`ProperSpace ℂ`）：arch 情形「复闭球」载体在现有 Mathlib
可直接陈述并证明（卡-A 缩减点 1 的「闭球」部分比报告所示更接近可用）。 -/
theorem complex_closedBall_isCompact (z : ℂ) (r : ℝ) :
    IsCompact (Metric.closedBall z r) :=
  isCompact_closedBall z r

end LeanFormal.IUT

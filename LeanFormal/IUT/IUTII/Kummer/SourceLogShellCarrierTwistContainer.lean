/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Set.Operations

/-!
# IUT-II log-shell 载体系：`(p*_v)^{-1}`-扭转容器律（载体件续；tmp 候选升正件）

本文件对位路线 B（I 层整构造）三缺之首「容器扭转」在**载体系**的残余形态：
`logs/coordination/monoanalytic-logshell-exploration-20261016.md` §13.4/§13.5
（「载体系 `logShell = (p*_v)^{-1} · preLogShell` 的 scaling 扭转」）。上游冻结件
`SourceLogShellCarrier.lean`（只读 import）已给出 `preLogShell ⊆ logShell`、两侧的
加法闭包与 `∃`-式集像等式 `logShell_eq_invScaledPreLogShell`；本文件补齐**扭转容器律**：
双向成员传递、`''`-式双向集像、`(p*_v)^{-1}`-扭转作为 `preLogShell → logShell` 的
双射（`Set.BijOn`）、加法与 `nsmul` 沿扭转的传输、具名谓词
`IsLogShellCarrierTwistContainer` 及其无条件居民与校准实例。

## 原文定位（沿用冻结件口径）

* [IUTchIII, Definition 1.1, (i)]（text l.1344-1351）：「the result of multiplying the
  pre-log-shell by the factor (p*_v)^{-1}」——本件即该句的集合论细化（集像、双射、运输律）。
* [IUTchIII, 引言, l.220-226]：`I_v` 两侧 Kummer 像；扭转律是 `I` 的容器形状部分。

## 边界（如实；不得顶替原文）

* 本件是**载体层扭转容器律**，非 I 层整构造：不证明 `I(αD⊢_vQ) ⊆ log(αD⊢_vQ)`、
  不构造混合包 I 层对象；arch `Ψcns` / `Ψ×_log` 维持 PARK（§11.7）。
* `invariants` 是子幺半群（逆一般不在内）：`logShell` 一般无负元、不构成 ℤ-模；
  本件只交付**加性幺半 + ℕ-标量**层，不冒充乘法容器（载体侧一般非乘性闭）。
  这两条是不可得边界，不以条件字段伪造。
* 消费者：route B I 层构造（容器扭转 / [Prop 1.2(vi)] 侧面对象 / `Ψcns`）。
-/

namespace LeanFormal.IUT

/-- ℕ-标量与乘法的交换律（交换半环）：`c * (n • y) = n • (c * y)`。
Mathlib 无此单条形状（`mul_nsmul'` 是 `(m * n) • a = m • (n • a)` 的不同形状）；
本件用于 `(p*_v)^{-1}`-扭转与 `nsmul` 的交换。 -/
theorem nsmul_mul_comm {α : Type*} [CommSemiring α] (c y : α) (n : ℕ) :
    c * (n • y) = n • (c * y) := by
  simp only [nsmul_eq_mul]
  ring

namespace SourceLogShellDatum

/-- `(p*_v)^{-1}`-扭转的双向成员律：`a ∈ log-shell ↔ p*_v · a ∈ pre-log-shell`
（[IUTchIII, Definition 1.1, (i)] 的等式 `I = (p*_v)^{-1} · pre-log-shell` 的成员读法；
冻结件 `logShell` 定义的直接展开）。 -/
theorem logShell_mem_iff_pStar_mul_mem (D : SourceLogShellDatum) (a : D.K) :
    a ∈ D.logShell ↔ (D.pStar : D.K) * a ∈ D.preLogShell :=
  Iff.rfl

/-- 扭转回收方向：`a ∈ log-shell → p*_v · a ∈ pre-log-shell`。 -/
theorem pStar_mul_mem_preLogShell_of_mem_logShell (D : SourceLogShellDatum) {a : D.K}
    (ha : a ∈ D.logShell) : (D.pStar : D.K) * a ∈ D.preLogShell :=
  ha

/-- 扭转施加方向：`x ∈ pre-log-shell → (p*_v)^{-1} · x ∈ log-shell`
（`p*_v ≠ 0` 给出 `p*_v · ((p*_v)^{-1} · x) = x`）。 -/
theorem pStar_inv_mul_mem_logShell_of_mem_preLogShell (D : SourceLogShellDatum) {x : D.K}
    (hx : x ∈ D.preLogShell) : (D.pStar : D.K)⁻¹ * x ∈ D.logShell := by
  change (D.pStar : D.K) * ((D.pStar : D.K)⁻¹ * x) ∈ D.preLogShell
  rwa [mul_inv_cancel_left₀ D.pStar_ne_zero_cast]

/-- 扭转集像等式（`''`-式）：`(p*_v)^{-1} · pre-log-shell = log-shell`。
与冻结 `∃`-式 `logShell_eq_invScaledPreLogShell` 同内容，供 `''`-重写与双射论证。 -/
theorem pStar_inv_image_preLogShell_eq_logShell (D : SourceLogShellDatum) :
    (fun x => (D.pStar : D.K)⁻¹ * x) '' D.preLogShell = D.logShell := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact D.pStar_inv_mul_mem_logShell_of_mem_preLogShell hx
  · intro hb
    exact ⟨(D.pStar : D.K) * b, D.pStar_mul_mem_preLogShell_of_mem_logShell hb,
      inv_mul_cancel_left₀ D.pStar_ne_zero_cast b⟩

/-- 扭转集像等式（反向）：`p*_v · log-shell = pre-log-shell`。 -/
theorem pStar_image_logShell_eq_preLogShell (D : SourceLogShellDatum) :
    (fun a => (D.pStar : D.K) * a) '' D.logShell = D.preLogShell := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact D.pStar_mul_mem_preLogShell_of_mem_logShell ha
  · intro hb
    exact ⟨(D.pStar : D.K)⁻¹ * b, D.pStar_inv_mul_mem_logShell_of_mem_preLogShell hb,
      mul_inv_cancel_left₀ D.pStar_ne_zero_cast b⟩

/-- 扭转双射：`x ↦ (p*_v)^{-1} · x` 是 `preLogShell → logShell` 的双射（`Set.BijOn`；
单射用 `p*_v ≠ 0` 的消去，满射由回收方向给出）。 -/
theorem pStar_inv_twist_bijOn (D : SourceLogShellDatum) :
    Set.BijOn (fun x => (D.pStar : D.K)⁻¹ * x) D.preLogShell D.logShell := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact D.pStar_inv_mul_mem_logShell_of_mem_preLogShell ha
  · intro a₁ _ a₂ _ h
    have h' : (D.pStar : D.K)⁻¹ * a₁ = (D.pStar : D.K)⁻¹ * a₂ := h
    calc a₁ = (D.pStar : D.K) * ((D.pStar : D.K)⁻¹ * a₁) :=
          (mul_inv_cancel_left₀ D.pStar_ne_zero_cast a₁).symm
      _ = (D.pStar : D.K) * ((D.pStar : D.K)⁻¹ * a₂) := by rw [h']
      _ = a₂ := mul_inv_cancel_left₀ D.pStar_ne_zero_cast a₂
  · intro b hb
    exact ⟨(D.pStar : D.K) * b, D.pStar_mul_mem_preLogShell_of_mem_logShell hb,
      inv_mul_cancel_left₀ D.pStar_ne_zero_cast b⟩

/-- `nsmul` 闭包（pre-log-shell 层）：`x ∈ pre-log-shell → n • x ∈ pre-log-shell`
（取 log 前像单位的 `n` 次幂；为冻结 `pow_smul_mem_preLogShell` 的集合层版本——后者由
`u ∈ invariants` 出发，前者对任意 `x ∈ pre` 提取见证）。 -/
theorem nsmul_mem_preLogShell (D : SourceLogShellDatum) {x : D.K}
    (hx : x ∈ D.preLogShell) (n : ℕ) : n • x ∈ D.preLogShell := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨u ^ n, D.invariants.pow_mem hu n, D.logMap_pow_val u n⟩

/-- `nsmul` 闭包（log-shell 层；容器律的 ℕ-标量部分）：`x ∈ log-shell → n • x ∈ log-shell`
（`p*_v · (n • x) = n • (p*_v · x)` 由 `nsmul_mul_comm` 给出）。 -/
theorem nsmul_mem_logShell (D : SourceLogShellDatum) {x : D.K}
    (hx : x ∈ D.logShell) (n : ℕ) : n • x ∈ D.logShell := by
  change (D.pStar : D.K) * (n • x) ∈ D.preLogShell
  rw [nsmul_mul_comm]
  exact D.nsmul_mem_preLogShell (D.pStar_mul_mem_preLogShell_of_mem_logShell hx) n

/-- 扭转的加法传输：`x, y ∈ pre-log-shell → (p*_v)^{-1} · (x + y) ∈ log-shell`
（分配律 `mul_add` 给出线性性，随后用冻结 `add_mem_logShell`）。 -/
theorem pStar_inv_twist_add_mem_logShell (D : SourceLogShellDatum) {x y : D.K}
    (hx : x ∈ D.preLogShell) (hy : y ∈ D.preLogShell) :
    (D.pStar : D.K)⁻¹ * (x + y) ∈ D.logShell := by
  rw [mul_add]
  exact D.add_mem_logShell (D.pStar_inv_mul_mem_logShell_of_mem_preLogShell hx)
    (D.pStar_inv_mul_mem_logShell_of_mem_preLogShell hy)

/-- 扭转的 `nsmul` 传输：`x ∈ pre-log-shell → n • ((p*_v)^{-1} · x) ∈ log-shell`
（`(p*_v)^{-1}`-扭转与 `nsmul` 可交换，再取 log-shell 的 `nsmul` 闭包）。 -/
theorem pStar_inv_twist_nsmul_mem_logShell (D : SourceLogShellDatum) {x : D.K}
    (hx : x ∈ D.preLogShell) (n : ℕ) :
    n • ((D.pStar : D.K)⁻¹ * x) ∈ D.logShell :=
  D.nsmul_mem_logShell (D.pStar_inv_mul_mem_logShell_of_mem_preLogShell hx) n

end SourceLogShellDatum

/-! ## 2. 扭转容器谓词（路线 B 阻断①残余的具名冻结形状） -/

/-- 「载体系扭转容器」谓词（冻结形状；§13 `IsLogShellFactorContainer` 的载体系对位）：
`0 ∈ pre`、`pre` 加闭、`logShell` 是 `(p*_v)^{-1}`-扭转的集像、双向成员律。
**本谓词对一切 `SourceLogShellDatum` 无条件成立**（见 `isLogShellCarrierTwistContainer`）；
不以假设代替证明。 -/
def IsLogShellCarrierTwistContainer (D : SourceLogShellDatum) : Prop :=
  (0 : D.K) ∈ D.preLogShell ∧
    (∀ x ∈ D.preLogShell, ∀ y ∈ D.preLogShell, x + y ∈ D.preLogShell) ∧
    D.logShell = (fun x => (D.pStar : D.K)⁻¹ * x) '' D.preLogShell ∧
    (∀ a : D.K, a ∈ D.logShell ↔ (D.pStar : D.K) * a ∈ D.preLogShell)

theorem IsLogShellCarrierTwistContainer.zero_mem {D : SourceLogShellDatum}
    (h : IsLogShellCarrierTwistContainer D) : (0 : D.K) ∈ D.preLogShell :=
  h.1

theorem IsLogShellCarrierTwistContainer.add_mem {D : SourceLogShellDatum}
    (h : IsLogShellCarrierTwistContainer D) {x : D.K} (hx : x ∈ D.preLogShell) {y : D.K}
    (hy : y ∈ D.preLogShell) : x + y ∈ D.preLogShell :=
  h.2.1 x hx y hy

theorem IsLogShellCarrierTwistContainer.logShell_eq_image {D : SourceLogShellDatum}
    (h : IsLogShellCarrierTwistContainer D) :
    D.logShell = (fun x => (D.pStar : D.K)⁻¹ * x) '' D.preLogShell :=
  h.2.2.1

theorem IsLogShellCarrierTwistContainer.mem_iff {D : SourceLogShellDatum}
    (h : IsLogShellCarrierTwistContainer D) (a : D.K) :
    a ∈ D.logShell ↔ (D.pStar : D.K) * a ∈ D.preLogShell :=
  h.2.2.2 a

/-- 居民定理：扭转容器谓词对一切载体数据**无条件**成立（`pre` 侧三条来自冻结件，
集像与成员律来自本件；无额外假设）。 -/
theorem isLogShellCarrierTwistContainer (D : SourceLogShellDatum) :
    IsLogShellCarrierTwistContainer D :=
  ⟨D.zero_mem_preLogShell, fun _ hx _ hy => D.add_mem_preLogShell hx hy,
    (D.pStar_inv_image_preLogShell_eq_logShell).symm, D.logShell_mem_iff_pStar_mul_mem⟩

/-! ## 3. 校准实例（`p*_2 = 4`；冻结件 §5 校准的直接消费） -/

/-- 校准：扭转容器谓词在 `v₂` 校准载体上成立（居民定理的直接特例）。 -/
theorem sourceLogShellCalibration_isCarrierTwistContainer :
    IsLogShellCarrierTwistContainer sourceLogShellCalibrationDatum :=
  isLogShellCarrierTwistContainer sourceLogShellCalibrationDatum

/-- 校准扭转点：`p*_2 · (1/2) = 2` 且 `(p*_2)^{-1} · 2 = 1/2`，同时
`2 ∈ pre-log-shell`、`1/2 ∈ log-shell`（冻结件 §5 校准律重组为一对扭转见证）。 -/
theorem sourceLogShellCalibration_twist_pair :
    (2 : ℚ) ∈ sourceLogShellCalibrationDatum.preLogShell ∧
      (1 / 2 : ℚ) ∈ sourceLogShellCalibrationDatum.logShell ∧
      (sourceLogShellCalibrationDatum.pStar : ℚ) * (1 / 2) = 2 ∧
      (sourceLogShellCalibrationDatum.pStar : ℚ)⁻¹ * 2 = 1 / 2 := by
  refine ⟨sourceLogShellCalibration_two_mem_preLogShell,
    sourceLogShellCalibration_half_mem_logShell, ?_, ?_⟩
  · rw [sourceLogShellCalibration_pStar_eq]
    norm_num
  · rw [sourceLogShellCalibration_pStar_eq]
    norm_num

/-- 校准成员律实例：`1/2 ∈ log-shell ↔ 2 ∈ pre-log-shell`（两侧在冻结件 §5 均无条件成立，
此处重组为 `↔` 形式；扭转方程本体见 `sourceLogShellCalibration_twist_pair`）。 -/
theorem sourceLogShellCalibration_twist_iff :
    (1 / 2 : ℚ) ∈ sourceLogShellCalibrationDatum.logShell ↔
      (2 : ℚ) ∈ sourceLogShellCalibrationDatum.preLogShell :=
  ⟨fun _ => sourceLogShellCalibration_two_mem_preLogShell,
    fun _ => sourceLogShellCalibration_half_mem_logShell⟩

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- 审计登记：log-shell 载体系 `(p*_v)^{-1}`-扭转容器律（`SourceLogShellCarrier` 续件；
路线 B 阻断①残余的最小件）。 -/
def sourceLogShellCarrierTwistContainer : Obligation :=
  { id := "IUT-II.source-log-shell-carrier-twist-container"
    source := "IUT III, Definition 1.1, (i) (text l.1330-1351); Introduction l.208-226"
    status := VerificationStatus.conditional
    note :=
      "Carrier-side (p*_v)^{-1}-twist container laws for the log-shell, appended to " ++
        "the frozen SourceLogShellCarrier. Proved unconditionally over the reduced " ++
        "carrier: the two-way membership law logShell_mem_iff_pStar_mul_mem, the " ++
        "scale/unscale memberships, the two function-image equalities (pre under " ++
        "x -> (p*_v)^{-1} x equals logShell; logShell under x -> p*_v x equals pre), " ++
        "the Set.BijOn statement of the twist, nsmul closures of pre and logShell, " ++
        "the additivity and nsmul transport of the twist, the named predicate " ++
        "IsLogShellCarrierTwistContainer with its unconditional inhabitant and the " ++
        "v_2 calibration witness (p*_2 = 4; 2 in pre, 1/2 in logShell, both twist " ++
        "equations). Boundary: carrier layer only; the invariant submonoid has no " ++
        "inverses in general, so there are no negative elements, no Z-module and no " ++
        "multiplicative container on the carrier side. Not delivered: the I-layer " ++
        "whole construction I(alphaD_vQ) subset log(alphaD_vQ), the mixed packet " ++
        "I(A, alphaD), the archimedean Psi^cns carrier and the Psi-times-log " ++
        "orbit/surjection card. See coordination report " ++
        "monoanalytic-logshell-exploration-20261016 section 14."
    dependsOn :=
      [ "IUT-II.source-log-shell-carrier",
        "IUT-II.vertical-log-kummer" ] }

end LeanFormal.IUT.Audit
